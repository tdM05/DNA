#!/usr/bin/env bash
# ============================================================================
# run_oracle_experiment.sh — driver for the LLM-ORACLE experiment. Runs the FULL
# faithfulness pipeline on ONE Euclid prop with an LLM filling the ORACLE role
# (map accept/reject + fill-stage gap adjudication), then grades once. See
# DESIGN_NOTES.md. Reuses the ablation driver's headless machinery verbatim; the
# only new parts are the phase state-machine and the two oracle gates.
#
# Usage:
#   bash run_oracle_experiment.sh --book 3 --prop 11 [--budget -1] [--model opus] [--max-map-rounds 5]
#
# ONE prop per invocation. The harness lives in the MAIN checkout; runs execute
# in the llm_oracle WORKTREE (so the worker can't read this harness). Re-running
# a prop is trivial — it auto-resets to the committed blank first.
# ============================================================================
set -uo pipefail
unset ANTHROPIC_API_KEY
set +u; source "$HOME/.venvs/leaneuclid/bin/activate"; set -u   # z3/cvc5 for lake build
. "$HOME/.elan/env" 2>/dev/null || export PATH="$HOME/.elan/bin:$PATH"   # lake on PATH (see ablation note)

# ---- CONFIG (edit here if paths/pins move) ---------------------------------
WORKTREE="/h/56/taddmao/code/autoform/methodology_compare_worktrees/llm_oracle"
BRANCH="llm_oracle_branch"                 # reset pin = this branch's committed Step-2 blank
OUT_BASE="/h/56/taddmao/code/autoform/DNA/reproducable_experiments/oracle_experiment/out"
MODEL_ID="claude-opus-4-8"                 # worker model
ORACLE_MODEL_ID="claude-opus-4-8"          # oracle model (plain Claude; cross-family is the post-hoc judge)
# The oracle is an AGENT that reads/investigates (map, SystemE, find.py) but must not MODIFY anything
# (it's a reviewer) — allow read/inspect tools, deny the mutating ones. git is denied via the
# worktree settings. It runs IN the worktree, which is fully blanked → no gold for it to find.
ORACLE_FLAGS=(--permission-mode acceptEdits --disallowedTools Edit Write NotebookEdit)
# The INTERVENE oracle (invoked when the worker gives up) MAY edit the map to repair a map-stage
# mistake, so edits are allowed; git is still denied by the worktree settings.
ORACLE_FIX_FLAGS=(--permission-mode acceptEdits)
MAX_INTERVENE=3     # max worker-giveup -> oracle-intervention cycles before the run is force-ended
RUN_MAX_SEC=36000                          # per <<<RUN>>> command cap (10h); agent idle meanwhile
RUN_MAX_BYTES=300000                       # feed whole RUN output; head+tail-trim only if larger
WALL_LIMIT_SEC=${WALL_LIMIT_SEC:-43200}    # 12h global hard wall (independent watchdog)
RETRY_SLEEP=${RETRY_SLEEP:-900}            # usage/rate-limit backoff (excluded from the wall)

# ---- locate self + worktree ------------------------------------------------
REPO="$WORKTREE"                           # all file/git ops target the worktree
LEP="$REPO/LeanEuclidPlus"
SCRIPTS="$LEP/scripts"
# Shared-state lock: step_signatures.json / assumption_tags.json are merged (read-modify-write) by
# check_steps.py --save and assumptions.py. When >1 prop runs at once in this shared worktree they'd
# race on those files, so we serialize those writes with an flock (exactly like scripts/safe_build.sh;
# flock works multi-node on this cluster's NFS, as the ablation's parallel builds relied on).
LOCKFILE="$LEP/.lake/oracle_shared.lock"
SLUG="$(echo "$REPO" | sed 's#[^a-zA-Z0-9]#-#g')"          # sessions/transcripts keyed to worktree cwd
# MEMORY is keyed to the git-common-dir ROOT (main repo), SHARED across worktrees — wipe THAT.
MEM_ROOT="$(cd "$REPO" && cd "$(git rev-parse --git-common-dir)/.." && pwd -P)"
MEMDIR="$HOME/.claude/projects/$(echo "$MEM_ROOT" | sed 's#[^a-zA-Z0-9]#-#g')/memory"

# ---- args ------------------------------------------------------------------
BOOK=""; PROP=""; BUDGET=-1; MODEL=opus; MAX_MAP_ROUNDS=5
while [ $# -gt 0 ]; do
  case "$1" in
    --book)           BOOK="${2:?}"; shift ;;
    --prop)           PROP="${2:?}"; shift ;;
    --budget)         BUDGET="${2:?}"; shift ;;
    --model)          MODEL="${2:?}"; shift ;;
    --max-map-rounds) MAX_MAP_ROUNDS="${2:?}"; shift ;;
    *) echo "unknown arg: $1"; exit 1 ;;
  esac; shift
done
{ [ -z "$BOOK" ] || [ -z "$PROP" ]; } && { echo "usage: --book N --prop NN [--budget -1] [--model opus] [--max-map-rounds 5]"; exit 1; }

UNLIMITED=0; BUDGET_DISP="\$$BUDGET"
[ "$BUDGET" = "-1" ] && { UNLIMITED=1; BUDGET_DISP="UNLIMITED (stops when worker finishes/gives up)"; }

NN="$(printf '%02d' "$PROP")"
PROPNUM="$((10#$PROP))"                      # unpadded — matches text file name & helper_<book>_<prop>_
rel="Book${BOOK}/Prop${NN}"
main="$LEP/$rel/Main.lean"
SRC_TXT="$LEP/Book${BOOK}/data/texts_proofs/${PROPNUM}.txt"   # canonical English (unpadded name)
label="Book${BOOK}_Prop${NN}_${MODEL}"

# ============================================================================
# PROMPTS — *** EDIT HERE ***  ($rel, $BOOK, $PROP, … filled at runtime)
# ============================================================================
GIVEUP_STRING="$rel of Book${BOOK} that I was assigned to work on: I confirm that I want to stop this attempt because I am not making progress."
GIVEUP_LINE="Give up ONLY if truly stuck — no viable path forward and continuing would just waste time/money. Do NOT give up merely because work is slow. To give up, print on its OWN line EXACTLY and nothing appended: $GIVEUP_STRING"
GUARDS="Your working directory is $REPO and you MUST stay strictly inside it. ANY command you run, ANY file you open/read, and ANY path you reference (absolute OR relative, directly or via cd/&&/;/|/subshell/wrapper) that points OUTSIDE $REPO — in particular ANY OTHER checkout of this project (a sibling 'DNA/', 'DNA-main/', or 'methodology_compare_worktrees/{full,od_only,ablated}/' directory) or anything under $REPO/reproducable_experiments/ (the eval harness) — DISQUALIFIES the attempt (AUTO-FAILED). This IS checked against your full transcript after the run; there is no benefit to looking, every proof outside your directory is irrelevant to your task. Also do NOT use git in ANY way (directly or via cd/&&/;/|/subshell/absolute path/wrapper); ANY git use DISQUALIFIES — AUTO-FAILED. No gaming the eval."
RUNCHAN_LINE="LONG COMMANDS (>10 min): a command you run yourself is force-killed after 10 minutes. For ANY command that may take longer (a slow build, check_step --all / --drive / --subtree, a long audit) do NOT run it yourself — END your turn with a block EXACTLY: a line '<<<RUN cwd=RELPATH>>>' (RELPATH a dir inside this repo relative to the repo root, usually 'LeanEuclidPlus'), the command on its own line(s), then '<<<END>>>'. The runner executes it with no time limit while you idle, then resumes you with its full output. This is NOT giving up. Use ONLY for long commands; run short ones normally."

# Phase A — the MAP only (no proving).
BRIEF_A="You are faithfully formalizing Euclid's Elements Book ${BOOK} Proposition ${PROP} in LeanEuclidPlus (System E), from scratch. The theorem SIGNATURE in LeanEuclidPlus/$rel/Main.lean is FIXED — never change it; the body is 'sorry'. PHASE A — produce the SENTENCE MAP ONLY, do NOT prove anything yet. Run the /faithful-split skill, then the /faithful-map skill, to turn Euclid's English proof text into the per-sentence 'euclid_sentence' map in Main.lean (every claim body stays ':= by sorry'), exactly as those skills prescribe (every sentence gets a REAL claim; restated givens become '-- @assumption' lines; a mid-proof 'I say that…' is euclid_wts). When the map is written and BOTH of these pass — 'python3 scripts/check_faithful.py --split $rel' (text tiling) and 'python3 scripts/check_step.py $rel --provable' (Main elaborates with sorry) — print on its OWN line EXACTLY: MAP_READY — then STOP; an ORACLE will review your map before you prove anything. Do NOT run /faithful-prove in this phase. $GUARDS $RUNCHAN_LINE $GIVEUP_LINE"

# Phase B — the FILL (sent after the oracle ACCEPTS the map and the assumption phase has run).
BRIEF_B="The ORACLE ACCEPTED your map, and the assumption phase has been run (every '-- @assumption' is now a materialized 'have'). PHASE B — prove every step with the /faithful-prove skill, driving with its '--drive' command: create the LeanEuclidPlus/$rel/stepN.lean backing files and prove each node until 'python3 scripts/check_step.py $rel --all' exits 0. Do NOT wire Main yourself — the harness wires it in Phase C. The 'euclid_sentence' CLAIM TYPES and the SIGNATURE are FROZEN — never change them. (If the assumption phase left a build error — usually a 'wlog … generalizing' frame break — run the /faithful-assumptions $rel skill to repair it first: NEVER delete a materialized 'have', add the redundant arg.) If a step is a GENUINE Euclid GAP (a fact Euclid read off the figure, NOT entailed by his hypotheses, FALSE in some admissible degenerate model — see CLAUDE.md's @euclid_gap rule; NEVER invent a System-E axiom), print on its OWN line EXACTLY: GAP_FLAG: <locator> :: <one-line why> — then STOP for oracle adjudication. When 'check_step.py $rel --all' exits 0, print on its OWN line EXACTLY: FILL_COMPLETE. $GUARDS $RUNCHAN_LINE $GIVEUP_LINE"

CONTINUE_A="Continue the MAP. You may NOT stop/pause/ask. The ONLY ways to end your turn: (1) print 'MAP_READY' on its own line once the map is written and the --split and --provable checks pass; (2) GIVE UP line; (3) a '<<<RUN cwd=…>>> … <<<END>>>' block. Otherwise keep working on the map."
CONTINUE_B="Continue PROVING. You may NOT stop/pause/ask. The ONLY ways to end your turn: (1) print 'FILL_COMPLETE' once 'check_step.py $rel --all' exits 0; (2) 'GAP_FLAG: <locator> :: <why>' for a genuine Euclid gap; (3) GIVE UP line; (4) a '<<<RUN cwd=…>>> … <<<END>>>' block. Otherwise keep proving."

# ============================================================================
# GATE 1 — the worktree must be on $BRANCH.
# ============================================================================
branch="$(git -C "$REPO" rev-parse --abbrev-ref HEAD)"
[ "$branch" = "$BRANCH" ] || { echo "ABORT: worktree $REPO is on '$branch', expected '$BRANCH'."; exit 1; }
[ -f "$SRC_TXT" ] || { echo "ABORT: no canonical text $SRC_TXT (invalid prop?)"; exit 1; }
[ -d "$LEP/SystemE/Theory" ] || { echo "ABORT: SystemE/Theory missing — oracle needs the axioms"; exit 1; }

# ============================================================================
# GATE 3 — reset the prop to the committed BLANK (signature + sorry), delete any
# files a previous run produced. Re-running is then trivial.
# ============================================================================
mkdir -p "$LEP/$rel"
git -C "$REPO" show "$BRANCH:LeanEuclidPlus/$rel/Main.lean" > "$main" 2>/dev/null \
  || { echo "ABORT: no $rel/Main.lean on $BRANCH (invalid prop?)"; exit 1; }
find "$LEP/$rel" -maxdepth 1 -type f ! -name Main.lean -delete
echo "[reset $rel to blank @ $BRANCH]"

RUN_ID="$(date +%Y%m%d-%H%M%S)-$( (cat /proc/sys/kernel/random/uuid 2>/dev/null || echo $RANDOM$RANDOM) | tr -d - | cut -c1-8)"
OUT="$OUT_BASE/$label/$RUN_ID"; mkdir -p "$OUT"
# The oracle runs IN the worktree ($REPO): the repo is fully BLANKED (no gold anywhere), so it can
# freely read the System E theory, run find.py, and open the map to judge — like a human oracle — and
# find no answers. The only gold is in sibling checkouts, guarded by the don't-leave-dir instruction
# + the post-hoc leak_check on its transcript (captured per call).

# git is already denied for the agent in the worktree's committed .claude/settings.json
# (permissions.deny has "Bash(git:*)" and "Bash(git)"), along with the shared-state writes
# (step_signatures.json / assumption_tags.json / proposition_signatures.json). Nothing to inject here.

# ---- MEMORY WIPE (shared main-repo memory; empty now; throwaway, idempotent, parallel-safe) ----
rm -rf "$MEMDIR" && echo "[memory wiped: $MEMDIR]"

WD=""
trap '[ -n "$WD" ] && kill -KILL "$WD" 2>/dev/null' EXIT

# ============================================================================
# agent_call — run a `claude -p …` ("$@"), retrying transparently on a usage/rate
# limit so no progress is lost. Sets global `out`. (Verbatim from the ablation.)
# ============================================================================
agent_call() {
  local rc is_err extra
  while :; do
    out="$("$@")"; rc=$?
    is_err="$(printf '%s' "$out" | jq -r '.is_error // empty' 2>/dev/null)"
    if [ "$rc" -ne 0 ] || { [ "$is_err" = true ] && \
         printf '%s' "$out" | grep -qiE 'usage limit|rate limit|limit reached|too many requests|(^|[^0-9])429([^0-9]|$)|resets? at|quota'; }; then
      echo "    ($rel: usage/rate limit (rc=$rc) — waiting ${RETRY_SLEEP}s, retrying same call; not counted)"
      extra="$(cat "$OUT/.wall_extra" 2>/dev/null)"; case "$extra" in ''|*[!0-9]*) extra=0 ;; esac
      echo $(( extra + RETRY_SLEEP )) > "$OUT/.wall_extra"
      sleep "$RETRY_SLEEP"; continue
    fi
    break
  done
}

# ============================================================================
# ORACLE — map review. An AGENT in the worktree (fully blanked → no gold to find):
# it reads the map, Euclid's text, and System E itself, and judges. One prompt, one
# JSON verdict. Sets ORACLE_DECISION (ACCEPT|REJECT|ERROR), ORACLE_FEEDBACK, ORACLE_LAST_COST.
# ============================================================================
oracle_map_review() {
  local round="$1" osid
  local prompt="You are the ORACLE reviewing the MAP STAGE of a faithful formalization of Euclid's Elements Book ${BOOK} Proposition ${PROP}. The map splits Euclid's natural-language proof into sentences s_1..s_n; each sentence s_i carries a single assertion assert(s_i) with assumptions assumptions(s_i). F(.) denotes the Lean formalization: the 'euclid_sentence' claim is F(assert(s_i)), and each '-- @assumption' entry above a sentence is an F(a) for some a in assumptions(s_i).
- Euclid's proof text: LeanEuclidPlus/Book${BOOK}/data/texts_proofs/${PROPNUM}.txt
- Proposed map: LeanEuclidPlus/$rel/Main.lean
Read both. You MAY read LeanEuclidPlus/SystemE/ and run 'python3 LeanEuclidPlus/scripts/find.py ...' to check what any predicate or axiom means.

You check EXACTLY these two conditions (verbatim from the paper's Table of Conditions; everything else is checked by scripts or Lean, NOT you):
  ATOMICITY:           s_i has a *single* assertion assert(s_i), with assumptions assumptions(s_i).
  ATOMIC FAITHFULNESS: for all a in assumptions(s_i), F(a) is faithful, and F(assert(s_i)) is faithful.
ACCEPT only if BOTH conditions hold for every sentence s_i; otherwise REJECT.

Do NOT look outside this directory — no other checkout of the project — and do NOT use git. Output ONLY a JSON object — NO markdown code fences, NO prose before or after — exactly this shape: {\"accept\": true, \"reasons\": \"per sentence: any ATOMICITY or ATOMIC FAITHFULNESS violation and why (or why both hold)\"}."
  osid="$(cat /proc/sys/kernel/random/uuid 2>/dev/null || python3 -c 'import uuid;print(uuid.uuid4())')"
  echo "    [oracle map-review round $round — agent in worktree]"
  cd "$REPO"
  local acc="" try=0
  agent_call claude -p "$prompt" --model "$ORACLE_MODEL_ID" --session-id "$osid" "${ORACLE_FLAGS[@]}" --output-format json
  while :; do
    echo "$out" > "$OUT/oracle_map_resp_${round}.json"
    ORACLE_LAST_COST="$(echo "$out" | jq -r '.total_cost_usd // 0')"
    ORACLE_SPENT="$(awk "BEGIN{print ${ORACLE_SPENT:-0}+${ORACLE_LAST_COST:-0}}")"
    acc="$(echo "$out" | jq -r '.result' | jq -r '.accept' 2>/dev/null)"
    ORACLE_FEEDBACK="$(echo "$out" | jq -r '.result' | jq -r '.reasons // ""' 2>/dev/null)"
    case "$acc" in true) ORACLE_DECISION=ACCEPT; break ;; false) ORACLE_DECISION=REJECT; break ;; esac
    try=$((try+1))
    [ "$try" -ge 3 ] && { ORACLE_DECISION=ERROR; ORACLE_FEEDBACK="oracle gave unparseable JSON 3x"; break; }
    echo "    (oracle reply unparseable — re-asking, try $try)"
    agent_call claude -p 'Your previous reply could not be parsed as JSON. Reply with ONLY a JSON object — NO markdown code fences, NO prose before or after — exactly: {"accept": true, "reasons": "..."}' --resume "$osid" --model "$ORACLE_MODEL_ID" "${ORACLE_FLAGS[@]}" --output-format json
  done
  cp "$PROJ/$osid.jsonl" "$OUT/oracle_map_${round}.transcript.jsonl" 2>/dev/null || true
  echo "    [oracle map-review round $round: $ORACLE_DECISION (oracle \$$ORACLE_LAST_COST)]"
}

# ============================================================================
# ORACLE — gap adjudication (same agent setup). Sets GAP_AGREE (yes|no|error), GAP_NOTE.
# ============================================================================
oracle_gap() {
  local loc="$1" why="$2" osid gc inner agree
  local prompt="You are the ORACLE adjudicating a suspected EUCLID GAP in the formalization of Book ${BOOK} Proposition ${PROP}. A Euclid gap is a fact Euclid USES but never states — true only in generic position and FALSE in some admissible degenerate configuration (diameter, collinear, coincident) — so it cannot be proved as stated without the case split he left implicit.
- Euclid's proof text: LeanEuclidPlus/Book${BOOK}/data/texts_proofs/${PROPNUM}.txt (read it; you may also read LeanEuclidPlus/SystemE/ and use scripts/find.py).
The prover flags the step at locator '$loc' as a gap, because: $why
Decide conservatively: is this a GENUINE Euclid gap (not entailed by his hypotheses + prior sentences, false in some admissible model), vs a fact that IS entailed and the prover merely failed to prove? Agree ONLY if genuinely false in some admissible configuration.
Do NOT look outside this directory and do NOT use git. Output ONLY a JSON object — NO markdown code fences, NO prose — exactly: {\"agree\": true, \"note\": \"short\"}."
  osid="$(cat /proc/sys/kernel/random/uuid 2>/dev/null || python3 -c 'import uuid;print(uuid.uuid4())')"
  cd "$REPO"
  local try=0
  agent_call claude -p "$prompt" --model "$ORACLE_MODEL_ID" --session-id "$osid" "${ORACLE_FLAGS[@]}" --output-format json
  while :; do
    echo "$out" > "$OUT/oracle_gap_resp_${gaps}.json"
    gc="$(echo "$out" | jq -r '.total_cost_usd // 0')"; ORACLE_SPENT="$(awk "BEGIN{print ${ORACLE_SPENT:-0}+${gc:-0}}")"
    agree="$(echo "$out" | jq -r '.result' | jq -r '.agree' 2>/dev/null)"
    GAP_NOTE="$(echo "$out" | jq -r '.result' | jq -r '.note // ""' 2>/dev/null)"
    case "$agree" in true) GAP_AGREE=yes; break ;; false) GAP_AGREE=no; break ;; esac
    try=$((try+1))
    [ "$try" -ge 3 ] && { GAP_AGREE=error; break; }
    echo "    (oracle gap reply unparseable — re-asking, try $try)"
    agent_call claude -p 'Your previous reply could not be parsed as JSON. Reply with ONLY a JSON object — NO markdown fences, NO prose — exactly: {"agree": true, "note": "..."}' --resume "$osid" --model "$ORACLE_MODEL_ID" "${ORACLE_FLAGS[@]}" --output-format json
  done
  cp "$PROJ/$osid.jsonl" "$OUT/oracle_gap_${gaps}.transcript.jsonl" 2>/dev/null || true
  echo "    [oracle gap-review $loc: $GAP_AGREE (oracle \$$gc)]"
}

# ============================================================================
# ORACLE — intervention after a worker GIVE-UP. The oracle (an agent that MAY EDIT
# the map) investigates whether the give-up is a map-stage mistake, fixes the map if
# so, and chooses an action. ONLY the oracle may truly end a run (action=giveup).
# Sets INTERVENE_ACTION (resume|restart_fill|giveup), INTERVENE_EDITED, INTERVENE_NOTE.
# ============================================================================
oracle_intervene() {
  local osid inner c ctx
  ctx="$(printf '%s' "$res" | tail -c 3500)"
  local prompt="You are the ORACLE. The worker gave up on Book ${BOOK} Proposition ${PROP} (phase: $state). Its last message:
<<<WORKER>>>
$ctx
<<<END>>>
Investigate what happened: read LeanEuclidPlus/$rel/Main.lean (the map), the proof text LeanEuclidPlus/Book${BOOK}/data/texts_proofs/${PROPNUM}.txt, LeanEuclidPlus/SystemE/, and run 'python3 LeanEuclidPlus/scripts/find.py ...' as needed. If you judge the map is at fault (a euclid_sentence claim, the sentence split, or an @assumption), you MAY edit it in LeanEuclidPlus/$rel/Main.lean to correct it; do NOT write proofs or stepN files (proving is the worker's job).
Then choose ONE action:
 - resume:       the worker should CONTINUE its current session (you fixed the map and/or your note tells it what to do).
 - restart_fill: you fixed the map; the fill stage should start FRESH.
 - giveup:       truly impossible or not worth continuing — this ENDS the run (ONLY you may end it this way).
Do NOT look outside this directory and do NOT use git. Output ONLY a JSON object — NO markdown code fences, NO prose — exactly: {\"action\": \"resume\", \"edited_map\": false, \"note\": \"what you changed and why, or why you give up\"}."
  osid="$(cat /proc/sys/kernel/random/uuid 2>/dev/null || python3 -c 'import uuid;print(uuid.uuid4())')"
  cd "$REPO"
  local try=0
  agent_call claude -p "$prompt" --model "$ORACLE_MODEL_ID" --session-id "$osid" "${ORACLE_FIX_FLAGS[@]}" --output-format json
  while :; do
    echo "$out" > "$OUT/oracle_intervene_${intervene}.json"
    c="$(echo "$out" | jq -r '.total_cost_usd // 0')"; ORACLE_SPENT="$(awk "BEGIN{print ${ORACLE_SPENT:-0}+${c:-0}}")"
    INTERVENE_ACTION="$(echo "$out" | jq -r '.result' | jq -r '.action' 2>/dev/null)"
    INTERVENE_EDITED="$(echo "$out" | jq -r '.result' | jq -r '.edited_map' 2>/dev/null)"
    INTERVENE_NOTE="$(echo "$out" | jq -r '.result' | jq -r '.note // ""' 2>/dev/null)"
    case "$INTERVENE_ACTION" in resume|restart_fill|giveup) break ;; esac
    try=$((try+1))
    [ "$try" -ge 3 ] && { INTERVENE_ACTION=giveup; INTERVENE_NOTE="intervene verdict unparseable 3x -> ending"; break; }
    echo "    (oracle intervene reply unparseable — re-asking, try $try)"
    agent_call claude -p 'Your previous reply could not be parsed as JSON. Reply with ONLY a JSON object — NO markdown fences, NO prose — exactly: {"action": "resume", "edited_map": false, "note": "..."}' --resume "$osid" --model "$ORACLE_MODEL_ID" "${ORACLE_FIX_FLAGS[@]}" --output-format json
  done
  cp "$PROJ/$osid.jsonl" "$OUT/oracle_intervene_${intervene}.transcript.jsonl" 2>/dev/null || true
  echo "    [oracle intervene #$intervene: action=$INTERVENE_ACTION edited_map=$INTERVENE_EDITED (oracle \$$c)]"
}

# ============================================================================
# GRADE (Phase C) — wire, then the per-prop gates (per-prop because sibling props
# are blanked; mirrors the ablation grade + wire_main prepended). Sets GRADE_FAIL.
# ============================================================================
grade() {
  local glog="$OUT/grade.log"; GRADE_FAIL=""
  { echo "===== GRADE $(date '+%F %T') · $rel · node=$(hostname 2>/dev/null) ====="; echo "worktree: $LEP"; echo; } > "$glog"

  echo "----- [wire_main] -----" >> "$glog"
  ( cd "$LEP" && timeout 3600 python3 scripts/wire_main.py "$rel" ) >> "$glog" 2>&1 \
    || { GRADE_FAIL="wire_main"; echo ">>> wire_main FAILED (–-all likely not clean)" >> "$glog"; return 1; }

  [ -f "$main" ] || { GRADE_FAIL="main_missing"; echo "FAIL: $main missing" >> "$glog"; return 1; }
  local sc; sc=$(grep -c 'sorry' "$main")
  { echo "----- [sorry_count] -----"; echo "sorry count = $sc (must be 0)"; echo; } >> "$glog"
  [ "$sc" -eq 0 ] || { GRADE_FAIL="sorry(count=$sc)"; echo "FAIL: $sc sorry in Main" >> "$glog"; return 1; }

  local mod="${rel//\//.}.Main"
  echo "----- [lake build $mod] -----" >> "$glog"
  ( cd "$LEP" && timeout 3600 lake build "$mod" ) >> "$glog" 2>&1 \
    || { GRADE_FAIL="lake_build"; echo ">>> lake_build FAILED" >> "$glog"; return 1; }
  # THOROUGH faithfulness: the authoritative olean check (faithful_export + check_faithful --olean),
  # book-aware, FOCUSED on this prop so the blanked sibling props don't interfere.
  echo "----- [check_faithful.sh $mod — olean, AUTHORITATIVE, focused] -----" >> "$glog"
  ( cd "$LEP" && scripts/check_faithful.sh "$mod" ) >> "$glog" 2>&1 \
    || { GRADE_FAIL="check_faithful_olean"; echo ">>> check_faithful.sh (olean, authoritative) FAILED" >> "$glog"; return 1; }
  echo "----- [check_backing] -----" >> "$glog"
  ( cd "$LEP" && python3 scripts/check_backing.py "$rel/Main.lean" ) >> "$glog" 2>&1 \
    || { GRADE_FAIL="check_backing"; echo ">>> check_backing FAILED" >> "$glog"; return 1; }
  echo "----- [check_signatures] -----" >> "$glog"
  ( cd "$LEP" && python3 scripts/check_signatures.py "$rel/Main.lean" ) >> "$glog" 2>&1 \
    || { GRADE_FAIL="check_signatures"; echo ">>> check_signatures FAILED" >> "$glog"; return 1; }
  echo "----- [check_steps vs oracle-approved baseline] -----" >> "$glog"
  ( cd "$LEP" && python3 scripts/check_steps.py "$rel/Main.lean" ) >> "$glog" 2>&1 \
    || { GRADE_FAIL="check_steps"; echo ">>> check_steps FAILED (claim drifted from approved map)" >> "$glog"; return 1; }
  echo "===== ALL CHECKS PASSED =====" >> "$glog"; return 0
}

# ============================================================================
# RUN — pre-generate the session id; phase state-machine loop.
# ============================================================================
cd "$REPO" || { echo "ABORT: cannot cd $REPO"; exit 1; }
PROJ="$HOME/.claude/projects/${SLUG}"
sid="$(cat /proc/sys/kernel/random/uuid 2>/dev/null || python3 -c 'import uuid;print(uuid.uuid4())')"
while [ -e "$PROJ/$sid.jsonl" ]; do sid="$(python3 -c 'import uuid;print(uuid.uuid4())')"; done
jsonl="$PROJ/$sid.jsonl"; t0=$(date +%s)
spent=0; ORACLE_SPENT=0; wall_ms=0; remaining="$BUDGET"; i=0; grade_sec=""; stop_reason=""
map_rounds=0; map_accepted=no; gaps=0; state=mapping; intervene=0; worker_call_mode=resume

write_result() {
  printf 'prop: %s\nmodel: %s\nsession_id: %s\ntranscript: %s\nworker_cost_usd: %s\noracle_cost_usd: %s\ntotal_cost_usd: %s\nwall_sec: %s\nmap_oracle_rounds: %s\nmap_accepted: %s\ngap_flags: %s\ncompile_sec: %s\nstop_reason: %s\nresult: %s\nfail_reason: %s\n' \
    "$rel" "$MODEL" "$sid" "$jsonl" "${spent:-0}" "${ORACLE_SPENT:-0}" "$(awk "BEGIN{print ${spent:-0}+${ORACLE_SPENT:-0}}")" \
    "$(awk "BEGIN{print ${wall_ms:-0}/1000}")" "$map_rounds" "$map_accepted" "$gaps" "${grade_sec:-<pending>}" "${stop_reason:-<pending>}" "$1" "${GRADE_FAIL:--}" \
    > "$OUT/result.txt"
}

write_result RUNNING
rm -f "$OUT/.wall_extra" 2>/dev/null
# 12h watchdog (verbatim from ablation: saves TIMEOUT + cancels the subtree)
_descendants() { local c; for c in $(pgrep -P "$1" 2>/dev/null); do [ "$c" = "$2" ] && continue; echo "$c"; _descendants "$c" "$2"; done; }
DRIVER_PID=$$
( self=$BASHPID
  while :; do
    extra="$(cat "$OUT/.wall_extra" 2>/dev/null)"; case "$extra" in ''|*[!0-9]*) extra=0 ;; esac
    left=$(( t0 + WALL_LIMIT_SEC + extra - $(date +%s) )); [ "$left" -le 0 ] && break; sleep "$left"
  done
  echo "    (GLOBAL ${WALL_LIMIT_SEC}s wall hit — saving TIMEOUT + cancelling)"
  kill -STOP "$DRIVER_PID" 2>/dev/null
  cp "$jsonl" "$OUT/transcript.jsonl" 2>/dev/null; cp -r "$LEP/$rel" "$OUT/" 2>/dev/null
  sed -i 's/^result: .*/result: TIMEOUT/; s/^stop_reason: .*/stop_reason: timeout_12h/' "$OUT/result.txt" 2>/dev/null
  pids="$(_descendants "$DRIVER_PID" "$self")"
  for p in $(printf '%s\n' $pids | tac); do kill -TERM "$p" 2>/dev/null; done; sleep 2
  for p in $pids; do kill -KILL "$p" 2>/dev/null; done
  kill -KILL "$DRIVER_PID" 2>/dev/null
) & WD=$!

echo "=== LLM-oracle · $rel · model=$MODEL · budget=$BUDGET_DISP · max_map_rounds=$MAX_MAP_ROUNDS · session $sid ==="
mb=(); [ "$UNLIMITED" = 1 ] || mb=(--max-budget-usd "$remaining")
agent_call claude -p "$BRIEF_A" --model "$MODEL_ID" --session-id "$sid" --permission-mode acceptEdits --output-format json ${mb[@]+"${mb[@]}"}
echo "$out" > "$OUT/round0.json"

while true; do
  tc=$(echo "$out" | jq -r '.total_cost_usd // 0'); spent=$(awk "BEGIN{print $spent+$tc}")
  [ "$UNLIMITED" = 1 ] || remaining=$(awk "BEGIN{print $BUDGET-$spent}")
  wall_ms=$(awk "BEGIN{print $wall_ms + $(echo "$out"|jq -r '.duration_ms // 0')}")
  write_result RUNNING
  if [ "$UNLIMITED" = 1 ]; then rem_disp="∞"; else rem_disp="\$$remaining"; fi
  echo "    $rel [$state] round $i: cost=\$$tc cum=\$$spent rem=$rem_disp subtype=$(echo "$out"|jq -r '.subtype')"
  res=$(echo "$out" | jq -r '.result')

  # ---- shared terminal checks (hard limits; a worker give-up is NOT one — see below) ----
  if [ "$UNLIMITED" = 0 ]; then
    [ "$(echo "$out"|jq -r '.subtype')" = error_max_budget_usd ] && { echo "    (budget cut)"; stop_reason=budget; break; }
    [ "$(awk "BEGIN{print ($remaining<=0.05)}")" = 1 ]           && { echo "    (budget exhausted)"; stop_reason=budget; break; }
  fi
  i=$((i+1)); [ "$i" -gt 300 ] && { echo "    (safety backstop — 300 rounds)"; stop_reason=backstop; break; }

  next_prompt=""

  # ---- worker GIVE-UP → ORACLE intervention (only the oracle may truly end the run) ----
  if printf '%s' "$res" | grep -qF "$GIVEUP_STRING"; then
    intervene=$((intervene+1))
    echo "    (worker gave up in [$state] — oracle intervention #$intervene)"
    if [ "$intervene" -gt "$MAX_INTERVENE" ]; then
      echo "    (exhausted $MAX_INTERVENE interventions)"; stop_reason=intervene_exhausted; break; fi
    oracle_intervene
    if [ "$INTERVENE_ACTION" = giveup ]; then
      echo "    (ORACLE ended the run: $INTERVENE_NOTE)"; stop_reason=oracle_giveup; break; fi
    # a map fix during the fill stage needs a fresh baseline + re-materialized assumptions
    if [ "$INTERVENE_EDITED" = true ] && [ "$state" = filling ]; then
      ( flock 9; cd "$LEP" && python3 scripts/check_steps.py --save "$rel/Main.lean" ) 9>"$LOCKFILE" > "$OUT/intervene_${intervene}_save.log" 2>&1 || true
      ( flock 9; cd "$LEP" && timeout 1800 python3 scripts/assumptions.py "$rel" ) 9>"$LOCKFILE" > "$OUT/intervene_${intervene}_assume.log" 2>&1 || true
    fi
    if [ "$INTERVENE_ACTION" = restart_fill ] && [ "$state" = filling ]; then
      cp "$jsonl" "$OUT/worker_pre_restart_${intervene}.transcript.jsonl" 2>/dev/null || true
      sid="$(cat /proc/sys/kernel/random/uuid 2>/dev/null || python3 -c 'import uuid;print(uuid.uuid4())')"
      jsonl="$PROJ/$sid.jsonl"; worker_call_mode=new
      next_prompt="$BRIEF_B"
    elif [ "$state" = mapping ]; then
      next_prompt="The ORACLE intervened (note: $INTERVENE_NOTE). Continue the MAP. $CONTINUE_A"
    else
      next_prompt="The ORACLE intervened and may have revised the MAP (note: $INTERVENE_NOTE). Re-read LeanEuclidPlus/$rel/Main.lean (claims/assumptions may have changed) and CONTINUE proving. $CONTINUE_B"
    fi
  fi

  # ---- <<<RUN>>> channel (state-independent; skipped if give-up already set next_prompt) ----
  if [ -z "$next_prompt" ]; then
  run_block="$(printf '%s' "$res" | sed -n '/<<<RUN/,/<<<END>>>/p')"
  if printf '%s' "$run_block" | grep -q '<<<RUN' && printf '%s' "$run_block" | grep -q '<<<END>>>'; then
    runcwd="$(printf '%s' "$run_block" | sed -n 's/.*<<<RUN[[:space:]]*cwd=\([^>]*\)>>>.*/\1/p' | head -1)"
    runcmd="$(printf '%s' "$run_block" | sed '1d;$d')"; [ -z "$runcwd" ] && runcwd="."
    abscwd="$( cd "$REPO" && cd "$runcwd" 2>/dev/null && pwd -P )" || abscwd=""
    case "$abscwd" in "$REPO"|"$REPO"/*) : ;; *) abscwd="" ;; esac
    if [ -n "$abscwd" ]; then
      runlog="$OUT/run$i.log"
      echo "    [RUN -> $runcwd (<=${RUN_MAX_SEC}s): $(printf '%s' "$runcmd" | tr '\n' ' ' | cut -c1-80)...]"
      ( cd "$abscwd" && timeout "$RUN_MAX_SEC" bash -c "$runcmd" ) > "$runlog" 2>&1; rc=$?
      sz=$(wc -c < "$runlog")
      if [ "$sz" -le "$RUN_MAX_BYTES" ]; then body="$(cat "$runlog")"
      else body="$(head -c $((RUN_MAX_BYTES/2)) "$runlog")
... [middle cut: output was $sz bytes; first+last $((RUN_MAX_BYTES/2))B shown — full in $runlog] ...
$(tail -c $((RUN_MAX_BYTES/2)) "$runlog")"; fi
      echo "    [RUN done -> exit $rc, ${sz}B]"
      case "$state" in filling) local_cont="$CONTINUE_B";; *) local_cont="$CONTINUE_A";; esac
      next_prompt="Output of your requested command (ran in '$runcwd', exit $rc):
$body

$local_cont"
    else
      case "$state" in filling) local_cont="$CONTINUE_B";; *) local_cont="$CONTINUE_A";; esac
      next_prompt="RUN request REFUSED: cwd '$runcwd' is empty or outside the repository. $local_cont"
    fi
  fi
  fi   # close the [ -z "$next_prompt" ] RUN-channel guard

  # ---- phase logic (only when there was no RUN block) ----
  if [ -z "$next_prompt" ]; then
    case "$state" in
    mapping)
      if echo "$res" | grep -qF "MAP_READY"; then
        # freeze the approved-map baseline for the grade's claim-type diff
        ( flock 9; cd "$LEP" && python3 scripts/check_steps.py --save "$rel/Main.lean" ) 9>"$LOCKFILE" > "$OUT/map_save_${map_rounds}.log" 2>&1 || true
        oracle_map_review "$map_rounds"
        if [ "$ORACLE_DECISION" = ACCEPT ]; then
          map_accepted=yes
          echo "    (oracle ACCEPTED the map after $map_rounds reject round(s))"
          # ---- Assumption phase (mechanical, no LLM). On failure, proceed anyway — BRIEF_B
          #      tells the worker to run /faithful-assumptions if the build is broken. ----
          echo "    [assumption phase: scripts/assumptions.py $rel]"
          ( flock 9; cd "$LEP" && timeout 1800 python3 scripts/assumptions.py "$rel" ) 9>"$LOCKFILE" > "$OUT/assumptions.log" 2>&1
          ar=$?; echo "assumptions.py exit=$ar" >> "$OUT/assumptions.log"
          [ "$ar" -eq 0 ] || echo "    (!! assumptions.py exit=$ar — worker will repair via /faithful-assumptions in fill)"
          state=filling; next_prompt="$BRIEF_B"
        elif [ "$ORACLE_DECISION" = ERROR ]; then
          echo "    (oracle ERROR — unparseable verdict; aborting prop)"; stop_reason=oracle_error; break
        else
          map_rounds=$((map_rounds+1))
          if [ "$map_rounds" -gt "$MAX_MAP_ROUNDS" ]; then
            echo "    (map did not converge in $MAX_MAP_ROUNDS oracle rounds)"; stop_reason=map_noconverge; break
          fi
          next_prompt="The ORACLE reviewed your map and did NOT accept it. Fix EVERY issue below (do NOT touch the fixed signature):
$ORACLE_FEEDBACK
When the map is corrected and 'check_faithful.py --split $rel' + 'check_step.py $rel --provable' pass again, print MAP_READY on its own line. $CONTINUE_A"
        fi
      else
        next_prompt="$CONTINUE_A"
      fi
      ;;
    filling)
      if echo "$res" | grep -qF "FILL_COMPLETE"; then
        echo "    (worker signalled FILL_COMPLETE)"; stop_reason=done; break
      elif echo "$res" | grep -qE "^GAP_FLAG:"; then
        gaps=$((gaps+1))
        gapline="$(printf '%s' "$res" | grep -E "^GAP_FLAG:" | head -1)"
        gloc="$(printf '%s' "$gapline" | sed -n 's/^GAP_FLAG:[[:space:]]*\([^:]*\)[[:space:]]*::.*/\1/p' | sed 's/[[:space:]]*$//')"
        gwhy="$(printf '%s' "$gapline" | sed -n 's/^GAP_FLAG:[^:]*::[[:space:]]*\(.*\)/\1/p')"
        echo "    [GAP_FLAG #$gaps: loc='$gloc' why='$gwhy']"
        oracle_gap "$gloc" "$gwhy"
        if [ "$GAP_AGREE" = yes ]; then
          next_prompt="The ORACLE AGREES $gloc is a genuine Euclid gap ($GAP_NOTE). Mark the site with a '-- @euclid_gap: <why>' comment and supply the case Euclid left implicit (by_cases/wlog; the degenerate branch is usually trivial), per CLAUDE.md. Then continue proving. $CONTINUE_B"
        else
          next_prompt="The ORACLE does NOT agree $gloc is a gap ($GAP_NOTE): it is entailed and provable. Do NOT mark @euclid_gap and NEVER invent a System-E axiom — prove it (decompose into backing files / euclid_apply). Continue proving. $CONTINUE_B"
        fi
      else
        next_prompt="$CONTINUE_B"
      fi
      ;;
    esac
  fi

  mb=(); [ "$UNLIMITED" = 1 ] || mb=(--max-budget-usd "$remaining")
  if [ "$worker_call_mode" = new ]; then     # fresh fill session (oracle chose restart_fill)
    agent_call claude -p "$next_prompt" --model "$MODEL_ID" --session-id "$sid" --permission-mode acceptEdits --output-format json ${mb[@]+"${mb[@]}"}
    worker_call_mode=resume
  else
    agent_call claude -p "$next_prompt" --resume "$sid" --model "$MODEL_ID" --permission-mode acceptEdits --output-format json ${mb[@]+"${mb[@]}"}
  fi
  echo "$out" > "$OUT/round$i.json"
done

[ -n "$WD" ] && kill -KILL "$WD" 2>/dev/null; WD=""
cp "$jsonl" "$OUT/transcript.jsonl" 2>/dev/null
cp -r "$LEP/$rel" "$OUT/" 2>/dev/null

# ---- outcome ----
status=FAIL; grade_sec=0; GRADE_FAIL=""
# git leak-guard: any git use by the agent DISQUALIFIES (overrides all)
git_hits="$( { jq -r '.. | .command? // empty' "$OUT/transcript.jsonl" 2>/dev/null
               jq -r '.. | .text? // empty'    "$OUT/transcript.jsonl" 2>/dev/null | sed -n '/<<<RUN/,/<<<END>>>/p'
             } | grep -nE '(^|[^A-Za-z0-9_])git([^A-Za-z0-9_]|$)' )"
if [ -n "$git_hits" ]; then
  status=FAIL; GRADE_FAIL="git_used"
  { echo "===== GIT LEAK-GUARD TRIPPED $(date '+%F %T') · $rel ====="; echo "AUTO-FAIL: agent ran git."; printf '%s\n' "$git_hits"; } > "$OUT/grade.log"
  echo "    (AUTO-FAIL: agent used git — DISQUALIFIED)"
elif [ "$stop_reason" = oracle_giveup ];      then status=ORACLE_GAVEUP; GRADE_FAIL="oracle_gaveup"
elif [ "$stop_reason" = intervene_exhausted ];then status=INCOMPLETE;    GRADE_FAIL="intervene_exhausted_${MAX_INTERVENE}"
elif [ "$stop_reason" = timeout_12h ];   then status=TIMEOUT;      GRADE_FAIL="wall_timeout_12h"
elif [ "$stop_reason" = map_noconverge ];then status=MAP_NOCONVERGE; GRADE_FAIL="map_noconverge_${MAX_MAP_ROUNDS}rounds"
elif [ "$stop_reason" = oracle_error ];  then status=ORACLE_ERROR; GRADE_FAIL="oracle_unparseable"
elif [ "$stop_reason" = budget ];        then status=FAIL;         GRADE_FAIL="budget_before_done"
else
  gt=$(date +%s); grade && status=SUCCESS; grade_sec=$(( $(date +%s) - gt ))
fi
write_result "$status"
echo "=== $rel -> $status  (stop=$stop_reason · worker=\$$spent oracle=\$$ORACLE_SPENT · map_rounds=$map_rounds · gaps=$gaps · $(( ($(date +%s)-t0)/60 ))m · compile ${grade_sec}s${GRADE_FAIL:+ · fail=$GRADE_FAIL}) · $OUT ==="
[ "$status" = SUCCESS ]

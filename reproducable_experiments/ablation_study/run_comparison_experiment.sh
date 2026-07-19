#!/usr/bin/env bash
# ============================================================================
# run_comparison_experiment.sh — the ONE driver for the methodology-comparison
# experiment. Runs a headless Claude agent on a SINGLE premapped Euclid prop and
# grades the result once. Two arms, selected by a required flag:
#
#   --ablated     naive bare-LLM arm   (worktree on branch: ablation_branch)
#   --my-method   full pipeline arm    (worktree on branch: full_methodology_branch)
#
# Both arms are driven by the SAME script (one copy per worktree, kept byte-
# identical — enforced at runtime, GATE 2). The two arms behave identically
# w.r.t. the harness: branch guard, self-consistency check, map-state gate,
# memory wipe, budget loop, single final grade. Only the task prompt and the
# per-arm branch/map-commit differ.
#
# The script AUTO-RESETS the target prop to its pinned map commit (GATE 3): it writes the map's
# Main.lean and deletes any other files in the prop folder, so a run needs no manual prep and
# re-running is trivial. CAVEAT: never run the SAME prop in two jobs at once (shared worktree folder).
#
# Usage:
#   bash run_comparison_experiment.sh --ablated   --book 1 --prop 47 [--budget 50] [--model opus]
#   bash run_comparison_experiment.sh --my-method --book 1 --prop 47 [--budget 50] [--model opus]
# ============================================================================
set -uo pipefail
unset ANTHROPIC_API_KEY
set +u; source "$HOME/.venvs/leaneuclid/bin/activate"; set -u   # z3/cvc5 on PATH for lake build

# ---- CONFIG (edit here if branches / map commits move) ---------------------
BRANCH_ABLATED="ablation_branch"
BRANCH_MYMETHOD="full_methodology_branch"
# Pinned MAP-STAGE commits — CANONICAL, per DNA/EXPERIMENT_OPERATOR_GUIDE.md.
# (The operator resets each prop's Main.lean to ITS map from these; GATE 3 checks it.)
MAP_REF_ABLATED="fa400f7"
MAP_REF_MYMETHOD="b98dd2b"
# CENTRAL results dir — OUTSIDE both worktrees so both arms' runs collect in one place (and other
# runs' outputs aren't sitting inside the agent's workspace). Same structure: out/<mode>/<label>/<run_id>/.
OUT_BASE="/h/56/taddmao/code/autoform/DNA/reproducable_experiments/ablation_study/out"

# ---- locate self + repo ----------------------------------------------------
SELF_DIR="$(cd "$(dirname "$0")" && pwd -P)"
SELF="$SELF_DIR/$(basename "$0")"
REPO="$(cd "$SELF_DIR/../.." && pwd -P)"
REL_SELF="${SELF#"$REPO"/}"                         # this script's path relative to repo root
LEP="$REPO/LeanEuclidPlus"
# Claude derives the project-dir name by replacing EVERY non-alphanumeric char
# (slashes AND underscores, dots, …) with '-', so the slug must match that or
# MEMDIR/PROJ point at a dir that doesn't exist.
SLUG="$(echo "$REPO" | sed 's#[^a-zA-Z0-9]#-#g')"
MEMDIR="$HOME/.claude/projects/${SLUG}/memory"

# ---- args ------------------------------------------------------------------
MODE=""; BOOK=""; PROP=""; BUDGET=50.00; MODEL=opus
while [ $# -gt 0 ]; do
  case "$1" in
    --ablated)   MODE=ablated ;;
    --my-method) MODE=mymethod ;;
    --book)      BOOK="${2:?}"; shift ;;
    --prop)      PROP="${2:?}"; shift ;;
    --budget)    BUDGET="${2:?}"; shift ;;
    --model)     MODEL="${2:?}"; shift ;;
    *) echo "unknown arg: $1"; exit 1 ;;
  esac; shift
done
[ -z "$MODE" ] && { echo "usage: run_comparison_experiment.sh --ablated|--my-method --book N --prop NN [--budget 50|-1] [--model opus]"; exit 1; }
{ [ -z "$BOOK" ] || [ -z "$PROP" ]; } && { echo "ERROR: --book and --prop are BOTH required (one prop per run)."; exit 1; }

# --budget -1 ⟹ UNLIMITED: no cost cap is passed to claude and no budget-based
# stop is applied. The run then ends ONLY when the agent finishes (emits the
# certification string) or gives up (once wired) — plus a large safety backstop.
UNLIMITED=0; BUDGET_DISP="\$$BUDGET"
if [ "$BUDGET" = "-1" ]; then UNLIMITED=1; BUDGET_DISP="UNLIMITED (stops only when agent finishes or gives up)"; fi

# select the arm's branch + map commit + the OTHER branch (for the self-consistency check)
if [ "$MODE" = ablated ]; then
  WANT_BRANCH="$BRANCH_ABLATED"; OTHER_BRANCH="$BRANCH_MYMETHOD"; MAP_REF="$MAP_REF_ABLATED"
else
  WANT_BRANCH="$BRANCH_MYMETHOD"; OTHER_BRANCH="$BRANCH_ABLATED"; MAP_REF="$MAP_REF_MYMETHOD"
fi

NN="$(printf '%02d' "$PROP")"
PROPNUM="$((10#$PROP))"                             # un-padded prop number, for the helper_<book>_<prop>_ name
rel="Book${BOOK}/Prop${NN}"
main="$LEP/$rel/Main.lean"
label="Book${BOOK}_Prop${NN}_${MODEL}"

# ============================================================================
# PROMPTS — *** EDIT HERE ***
# PROMPT is the VERBATIM manual (operator-guide) task prompt. The interactive
# runs used `/goal` to judge "done" and a human to re-nudge a stall; headless
# has neither, so the two additions are:
#   • two completion signals — CERT_STRING (done) and GIVEUP_STRING (not making
#     progress) — announced to the agent via CERT_LINE / GIVEUP_LINE, and
#   • CONTINUE_PROMPT, resent every resume turn, which forbids stopping unless
#     the turn ends with one of those two exact lines.
# The run loop greps the agent's final message: CERT → grade the result;
# GIVEUP → mark NOT complete and SKIP the grade (per the operator design).
# Shell placeholders ($rel, $BOOK, $PROP, …) are filled at runtime.
# ============================================================================
# The two exact terminal strings the agent must print verbatim (these replace /goal).
CERT_STRING="$rel of Book${BOOK} that I was assigned to work on, is completely done. I certify it is faithful, compiles with no sorry, and is ready for review."
GIVEUP_STRING="$rel of Book${BOOK} that I was assigned to work on: I confirm that I want to stop this attempt because I am not making progress."
CERT_LINE="When it is completely done, print on its OWN line EXACTLY this and nothing appended: $CERT_STRING"
GIVEUP_LINE="Give up ONLY if you judge you are truly stuck — you see no viable path forward and continuing would just waste time and money. Do NOT give up merely because the work is slow or takes many steps: steady progress, however slow, means keep going. If you do decide to give up, print on its OWN line EXACTLY this and nothing appended: $GIVEUP_STRING"

if [ "$MODE" = mymethod ]; then
  # --my-method: verbatim operator-guide "Full" prompt + the two completion signals.
  PROMPT="Prove LeanEuclidPlus/$rel/Main.lean end to end using /faithful-prove skill. As usual make sure --all passes, and please also wire it at the end. DO NOT read anything OUTSIDE this repository ($REPO), and DO NOT read anything under $REPO/reproducable_experiments/ (that is the experiment harness / eval). Doing either DISQUALIFIES the attempt — AUTO-FAILED. No gaming the eval. $CERT_LINE $GIVEUP_LINE"
else
  # --ablated: operator-guide "Ablated" prompt + REQUIRED per-sentence backing-file structure (so the
  # skill-less arm produces the same decomposition the eval now checks) + the two completion signals.
  PROMPT="Prove LeanEuclidPlus/$rel/Main.lean — fill every ':= by sorry' so it builds with ZERO sorry. Do NOT change the theorem statement, the '(stepN : …)' claim types, or the '-- @assumption (…)' lines. Also anything euclid cites, must be cited as well in Lean. Note that the venv is at ~/.venvs/leaneuclid/bin/activate for z3 and cvc5. REQUIRED STRUCTURE (this is checked — do NOT prove any sentence inline): for each 'euclid_sentence \"…\" (stepK : CLAIM) := by sorry', (1) create a new file LeanEuclidPlus/$rel/stepK.lean holding ONE lemma 'theorem helper_${BOOK}_${PROPNUM}_stepK (…binders…) : CLAIM := by …' that proves that step (euclid_finish is fine INSIDE the helper), taking whatever facts it needs as hypotheses; (2) add 'import Book${BOOK}.Prop${NN}.stepK' at the top of Main.lean; (3) make Main's body delegate, supplying EVERY hypothesis via euclid_assumption with its type shown — EXACTLY '(by euclid_assumption \"TEXT\" (show TYPE; assumption))', NEVER a bare '(by assumption)'. If a hypothesis has a '-- @assumption (\"NL-TEXT\", TYPE)' line above the sentence, use that NL-TEXT verbatim as the string (so it is clear WHERE that cited fact is used); for the other hypotheses use the empty string \"\". Schematic: in Main '(stepK : CLAIM) := by euclid_apply (helper_${BOOK}_${PROPNUM}_stepK o1 o2 (by euclid_assumption \"the exact @assumption text\" (show TYPE1; assumption)) (by euclid_assumption \"\" (show TYPE2; assumption)))', and in stepK.lean 'theorem helper_${BOOK}_${PROPNUM}_stepK (o1 …) (h1 : TYPE1) (h2 : TYPE2) : CLAIM := by euclid_finish'. DO NOT read anything OUTSIDE this repository ($REPO), and DO NOT read anything under $REPO/reproducable_experiments/ (that is the experiment harness / eval). Doing either DISQUALIFIES the attempt — AUTO-FAILED. No gaming the eval. $CERT_LINE $GIVEUP_LINE"
fi

# Sent on EVERY resume turn — the headless stand-in for the human re-nudging a
# stalled interactive session (the "I did 60%, continue?" case). It forbids
# stopping unless the turn ends with one of the two exact terminal lines.
CONTINUE_PROMPT="Continue working on the task. You are NOT allowed to stop, pause, or ask for confirmation or permission. The ONLY way you may end your turn is to output, on its own line, EXACTLY one of these two lines verbatim: (1) DONE — \"$CERT_STRING\"  or  (2) GIVE UP — \"$GIVEUP_STRING\". Being slow or taking many steps is NOT a reason to give up — only give up if there is no viable path forward and continuing would just waste time and money. Until you print one of those two lines, keep working on your own."

# ============================================================================
# GATE 1 — branch guard: this worktree must be on the arm's branch.
# ============================================================================
branch="$(git -C "$REPO" rev-parse --abbrev-ref HEAD)"
[ "$branch" = "$WANT_BRANCH" ] || {
  echo "ABORT: --$MODE must run on '$WANT_BRANCH', but this worktree is on '$branch'."
  echo "       cd into the correct worktree (see DNA/EXPERIMENT_OPERATOR_GUIDE.md) and retry."; exit 1; }

# ============================================================================
# GATE 2 — self-consistency: this driver must be byte-identical in BOTH
# worktrees ("one script drives all"). Locate the OTHER worktree by its branch
# and diff the same-relative-path copy against this one.
# ============================================================================
OTHER_WT="$(git -C "$REPO" worktree list --porcelain | awk -v b="refs/heads/$OTHER_BRANCH" '
  /^worktree /{wt=substr($0,10)} /^branch /{if(substr($0,8)==b) print wt}')"
[ -n "$OTHER_WT" ] || { echo "ABORT: could not locate the '$OTHER_BRANCH' worktree via 'git worktree list'."; exit 1; }
OTHER_SELF="$OTHER_WT/$REL_SELF"
[ -f "$OTHER_SELF" ] || { echo "ABORT: sibling driver missing in the other worktree: $OTHER_SELF"; exit 1; }
diff -q "$SELF" "$OTHER_SELF" >/dev/null 2>&1 || {
  echo "ABORT: this driver DIFFERS from the '$OTHER_BRANCH' copy:"
  echo "         $SELF"
  echo "         $OTHER_SELF"
  echo "       They must be identical — one script drives both arms. Reconcile them first"
  echo "       (diff the two files), then retry."; exit 1; }

# ============================================================================
# GATE 3 — map-state: AUTO-RESET this prop to its map. Write the map's Main.lean and delete every
# other file in the prop folder, so the run starts from a clean blank map with NO manual prep — and
# re-running is trivial (just launch again). CAVEAT: never run the SAME prop in two jobs at once —
# they share this one worktree folder and would clobber each other.
# ============================================================================
mkdir -p "$LEP/$rel"
git -C "$REPO" show "$MAP_REF:LeanEuclidPlus/$rel/Main.lean" > "$main" 2>/dev/null \
  || { echo "ABORT: no $rel/Main.lean in map $MAP_REF (invalid prop?)"; exit 1; }
find "$LEP/$rel" -maxdepth 1 -type f ! -name Main.lean -delete
echo "[reset $rel to map $MAP_REF — blank Main.lean, no step files]"

echo "=== comparison experiment · mode=$MODE · branch=$branch · $rel · model=$MODEL · budget=$BUDGET_DISP ==="
echo "    [gate 1: branch OK]  [gate 2: driver identical to $OTHER_BRANCH copy]  [gate 3: Main.lean == map $MAP_REF]"

# Each invocation is ONE run with a UNIQUE id + start datetime, in its OWN folder under the prop's
# label dir — so the 3 repeat runs per prop coexist and stay identifiable (never overwrite each other).
RUN_ID="$(date +%Y%m%d-%H%M%S)-$( (cat /proc/sys/kernel/random/uuid 2>/dev/null || echo $RANDOM$RANDOM) | tr -d - | cut -c1-8)"
OUT="$OUT_BASE/$MODE/$label/$RUN_ID"; mkdir -p "$OUT"         # <central>/out/<mode>/Book1_Prop47_opus/<datetime>-<id>/

# ============================================================================
# LEAK GUARD — deny ALL git for the AGENT so it can't `git show`/`git log` the
# finished proof out of history. Add-only + idempotent (inserts the rules into
# permissions.deny iff missing, preserving formatting). The SCRIPT's own git is
# UNAFFECTED — the deny gates only Claude's Bash tool, not this shell. NOT
# auto-removed: to restore read-only git, `git checkout -- .claude/settings.json`.
# ============================================================================
python3 - "$REPO/.claude/settings.json" <<'PY'
import sys
p = sys.argv[1]
try:
    s = open(p).read()
except FileNotFoundError:
    print("!! no %s — skipping git leak-guard" % p); sys.exit(0)
need = [r for r in ('"Bash(git:*)"', '"Bash(git)"') if r not in s]
if not need:
    print("[leak-guard: git already denied for agent]"); sys.exit(0)
i = s.index('"deny": [') + len('"deny": [')          # top of the deny array
block = "".join('\n      %s,' % r for r in need)
if s[i:].lstrip().startswith(']'):                    # empty deny array → no trailing comma
    block = block.rstrip(',')
s = s[:i] + block + s[i:]
open(p, "w").write(s)
print("[leak-guard: denied git for agent -> %s]" % ", ".join(need))
PY

# ============================================================================
# MEMORY WIPE — DELETE the project's memory dir before the run (both arms), so
# no accumulated answer-notes leak in. Plain delete, NOT a hide/restore: no
# trap, no rename, so parallel runs can't race on it and there is nothing to
# leave behind on a crash. Not restored — intended; these are throwaway runs.
# (No-op if the dir doesn't exist.)
# ============================================================================
rm -rf "$MEMDIR" && echo "[memory deleted: $MEMDIR]"

# Heartbeat pid — killed on any exit (normal, Ctrl-C, kill) so it never orphans.
HB=""
trap '[ -n "$HB" ] && kill "$HB" 2>/dev/null' EXIT

# ============================================================================
# GRADE (identical for both arms): 0 sorry + faithful (texts/citations/structure) + per-sentence
# backing lemma + signature unchanged + claim/@assumption types unchanged + compiles ≤1h. Run ONCE at
# the end, never fed back to the agent (no oracle).
# NOTE: check_faithful stays --relaxed (drops the methodology-only bulk-tactic ban + assumption tag
# gate — we do NOT force assumption structure). The ONE extra faithfulness criterion held equal for
# both arms is the per-sentence backing lemma (check_backing.py); the full method auto-satisfies it.
# ============================================================================
grade() {
  [ -f "$main" ] || return 1
  [ "$(grep -c 'sorry' "$main")" -eq 0 ] || return 1
  ( cd "$LEP" && python3 scripts/check_faithful.py  --relaxed "$rel/Main.lean" >/dev/null 2>&1 ) || return 1
  ( cd "$LEP" && python3 scripts/check_backing.py            "$rel/Main.lean" >/dev/null 2>&1 ) || return 1
  ( cd "$LEP" && python3 scripts/check_signatures.py         "$rel/Main.lean" >/dev/null 2>&1 ) || return 1
  ( cd "$LEP" && python3 scripts/check_steps.py     --relaxed "$rel/Main.lean" >/dev/null 2>&1 ) || return 1
  ( cd "$LEP" && timeout 3600 lake build "${rel//\//.}.Main"                   >/dev/null 2>&1 ) || return 1
  return 0
}

# ============================================================================
# RUN the agent (budget loop) — pre-generate a fresh, unique session id so its
# id + transcript path are known from t=0. Loop `claude -p --resume` until the
# certification string appears (or the budget is cut / a safety backstop hits).
# ============================================================================
# Pin the agent's cwd to the WORKTREE ROOT (full/ or ablated/). CLAUDE.md +
# project settings load relative to cwd, and the prompt's paths (LeanEuclidPlus/…)
# are repo-root-relative, so every run must start here regardless of where the
# operator invoked the script. (grade() cd's to $LEP only inside subshells.)
cd "$REPO" || { echo "ABORT: cannot cd to repo root $REPO"; exit 1; }

PROJ="$HOME/.claude/projects/${SLUG}"
sid="$(cat /proc/sys/kernel/random/uuid 2>/dev/null || python3 -c 'import uuid;print(uuid.uuid4())')"
while [ -e "$PROJ/$sid.jsonl" ]; do sid="$(python3 -c 'import uuid;print(uuid.uuid4())')"; done
jsonl="$PROJ/$sid.jsonl"
t0=$(date +%s)

write_result() { # $1 = status
  printf 'prop: %s\nmode: %s\nmodel: %s\nsession_id: %s\ntranscript: %s\ncost_usd: %s\nwall_sec: %s\ncompile_sec: %s\nstop_reason: %s\nresult: %s\n' \
    "$rel" "$MODE" "$MODEL" "$sid" "$jsonl" "${spent:-0}" "$(awk "BEGIN{print ${wall_ms:-0}/1000}")" "${grade_sec:-<pending>}" "${stop_reason:-<pending>}" "$1" \
    > "$OUT/result.txt"
}

# heartbeat → _current.txt: session id + transcript + elapsed, from t=0.
( while :; do e=$(( $(date +%s) - t0 ))
    printf '%s  %s  %s  session=%s  transcript=%s  elapsed=%dm%02ds  (started %s · Ctrl-C to cancel)\n' \
      "$rel" "$MODE" "$MODEL" "$sid" "$jsonl" $((e/60)) $((e%60)) "$(date -d @"$t0" +%H:%M:%S)" \
      > "$OUT_BASE/$MODE/_current.txt"
    sleep 15; done ) &
HB=$!

spent=0; wall_ms=0; remaining="$BUDGET"; i=0; grade_sec=""; stop_reason=""
write_result RUNNING
echo "--- $rel: starting (budget=$BUDGET_DISP · no time limit · session $sid) ---"
mb=(); [ "$UNLIMITED" = 1 ] || mb=(--max-budget-usd "$remaining")   # cost cap arg — omitted entirely when unlimited
out=$(claude -p "$PROMPT" --model "$MODEL" --session-id "$sid" --permission-mode acceptEdits --output-format json ${mb[@]+"${mb[@]}"})
echo "$out" > "$OUT/round0.json"
while true; do
  tc=$(echo "$out" | jq -r '.total_cost_usd // 0')
  spent=$(awk "BEGIN{print $spent+$tc}")
  [ "$UNLIMITED" = 1 ] || remaining=$(awk "BEGIN{print $BUDGET-$spent}")
  wall_ms=$(awk "BEGIN{print $wall_ms + $(echo "$out"|jq -r '.duration_ms // 0')}")
  write_result RUNNING
  if [ "$UNLIMITED" = 1 ]; then rem_disp="∞"; else rem_disp="\$$remaining"; fi
  echo "    $rel round $i: cost=\$$tc cumulative=\$$spent remaining=$rem_disp subtype=$(echo "$out"|jq -r '.subtype')"
  res=$(echo "$out" | jq -r '.result')
  if echo "$res" | grep -qF "$CERT_STRING";   then echo "    (agent signalled DONE)";     stop_reason=done;   break; fi
  if echo "$res" | grep -qF "$GIVEUP_STRING"; then echo "    (agent signalled GIVE UP)";  stop_reason=gaveup; break; fi
  if [ "$UNLIMITED" = 0 ]; then
    [ "$(echo "$out"|jq -r '.subtype')" = error_max_budget_usd ] && { echo "    (budget cut)";       stop_reason=budget; break; }
    [ "$(awk "BEGIN{print ($remaining<=0.05)}")" = 1 ]           && { echo "    (budget exhausted)"; stop_reason=budget; break; }
  fi
  i=$((i+1)); [ "$i" -gt 300 ] && { echo "    (safety backstop — 300 rounds)"; stop_reason=backstop; break; }
  mb=(); [ "$UNLIMITED" = 1 ] || mb=(--max-budget-usd "$remaining")
  out=$(claude -p "$CONTINUE_PROMPT" --resume "$sid" --model "$MODEL" --permission-mode acceptEdits --output-format json ${mb[@]+"${mb[@]}"})
  echo "$out" > "$OUT/round$i.json"
done
kill "$HB" 2>/dev/null; HB=""
cp "$jsonl" "$OUT/transcript.jsonl" 2>/dev/null
# Snapshot the produced Prop folder (Main.lean + step*.lean) INTO the run folder — self-contained, and
# it survives the next repeat's reset. Kept for later (controlled) build-time experiments on the artifact.
cp -r "$LEP/$rel" "$OUT/" 2>/dev/null                         # → $OUT/Prop<NN>/

# ---- outcome: give-up ⟹ NOT complete, no grade; anything else ⟹ grade once --
status=FAIL; grade_sec=0
if [ "$stop_reason" = gaveup ]; then
  status=GAVEUP
  echo "    (agent gave up — marked NOT complete, grade skipped)"
else
  gt=$(date +%s)
  grade && status=SUCCESS
  grade_sec=$(( $(date +%s) - gt ))
fi
write_result "$status"
echo "=== $rel -> $status  (stop=$stop_reason · \$$spent · $(( ($(date +%s)-t0)/60 ))m wall · compile ${grade_sec}s) ==="
[ "$status" = SUCCESS ]

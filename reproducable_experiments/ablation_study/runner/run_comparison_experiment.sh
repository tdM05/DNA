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
set +u; source "$HOME/.venvs/euclid/bin/activate"; set -u   # z3/cvc5 on PATH (SMT solvers for lake build)
# lake itself comes from ELAN, not the venv. A non-login SLURM shell does NOT have ~/.elan/bin on PATH
# (it only arrives via `sbatch --export=ALL` IF the submitting shell happened to have it — fragile). Put
# it on PATH explicitly so the grade's `lake build` AND the agent's builds always find lake. Fixes the
# intermittent `timeout: failed to run command 'lake': No such file or directory` grade failures.
. "$HOME/.elan/env" 2>/dev/null || export PATH="$HOME/.elan/bin:$PATH"

# ---- CONFIG (edit here if branches / map commits move) ---------------------
BRANCH_ABLATED="ablation_branch"
BRANCH_MYMETHOD="full_methodology_branch"
# Pinned MAP-STAGE commits — CANONICAL (see runner/README.md).
# (The operator resets each prop's Main.lean to ITS map from these; GATE 3 checks it.)
MAP_REF_ABLATED="fa400f7"
MAP_REF_MYMETHOD="b98dd2b"
# CENTRAL results dir — OUTSIDE both worktrees so both arms' runs collect in one place (and other
# runs' outputs aren't sitting inside the agent's workspace). Same structure: out/<mode>/<label>/<run_id>/.
OUT_BASE="/home/user/code/autoform/DNA/reproducable_experiments/ablation_study/out"
# Long-command channel: a command the agent runs itself in its shell is force-killed at 10 min. When it
# instead ends a turn with a `<<<RUN cwd=… >>> … <<<END>>>` block, the DRIVER runs that command here
# (no per-call time cap — the agent sits idle meanwhile) and feeds the output back on the next resume.
# This is the headless stand-in for interactive "launch in background, get woken when done": the driver
# is the supervisor that outlives the turn. The FULL output is fed back (like an interactive tool
# result); only if it exceeds RUN_MAX_BYTES is it head+tail-trimmed so a runaway log can't break the
# API request. RUN_MAX_SEC caps one such command.
RUN_MAX_SEC=36000            # 10h ceiling for one agent-requested command (the agent's constant cap)
RUN_MAX_BYTES=300000         # feed the WHOLE output; head+tail-trim only if larger than this (~75k tok)
# 12h GLOBAL HARD WALL for the whole run. Completely independent of RUN_MAX_SEC and of the agent loop —
# the agent always "has" its full 10h RUN cap, and nothing in the round loop knows about this wall. It is
# enforced by ONE separate background WATCHDOG (spawned near the run start, defined below): it sleeps until
# t0+12h and, if it fires, saves the run (transcript + PropNN snapshot + result=TIMEOUT, exactly like the
# manual fixup) and then cancels EVERYTHING (agent + build + driver). No crash. A normal finish reaps it.
WALL_LIMIT_SEC=${WALL_LIMIT_SEC:-43200}   # 12h default; override via env for a quick test, e.g. WALL_LIMIT_SEC=180
# SUBSCRIPTION USAGE RETRY. When `claude -p` returns a usage/rate-limit error (the subscription cap is hit),
# that round is NOT counted — the driver sleeps RETRY_SLEEP and re-issues the SAME resume (same session) until
# the quota returns, so no progress is lost. The wait is EXCLUDED from the 12h wall: each wait bumps
# $OUT/.wall_extra and the watchdog pushes its deadline out by that much, so an outage can't cause a spurious
# TIMEOUT. Measured wall_sec is unaffected too — it sums real rounds' duration_ms; skipped error rounds add none.
RETRY_SLEEP=${RETRY_SLEEP:-900}           # 15 min between usage-limit retries (override via env for a test)

# ---- locate self + repo ----------------------------------------------------
SELF_DIR="$(cd "$(dirname "$0")" && pwd -P)"
SELF="$SELF_DIR/$(basename "$0")"
REPO="$(cd "$SELF_DIR/../.." && pwd -P)"
REL_SELF="${SELF#"$REPO"/}"                         # this script's path relative to repo root
LEP="$REPO/LeanEuclidPlus"
# Claude derives the project-dir name by replacing EVERY non-alphanumeric char (slashes, underscores,
# dots, …) with '-'. SESSIONS/TRANSCRIPTS live under the WORKTREE's slug (used by PROJ, below) — correct.
SLUG="$(echo "$REPO" | sed 's#[^a-zA-Z0-9]#-#g')"
# MEMORY is DIFFERENT: Claude keys it to the GIT REPO ROOT (the main repo), SHARED across all worktrees —
# resolved via git-common-dir, NOT the worktree cwd. So MEMDIR must use the repo-root slug, else the pre-run
# wipe targets a nonexistent worktree-slug dir (silent no-op) and the real memory LEAKS into every run.
MEM_ROOT="$(cd "$REPO" && cd "$(git rev-parse --git-common-dir)/.." && pwd -P)"
MEMDIR="$HOME/.claude/projects/$(echo "$MEM_ROOT" | sed 's#[^a-zA-Z0-9]#-#g')/memory"

# ---- args ------------------------------------------------------------------
MODE=""; BOOK=""; PROP=""; BUDGET=50.00; MODEL=opus
MODEL_ID="us.anthropic.claude-opus-4-8[1m]"   # real Bedrock id passed to `claude --model`; MODEL stays the folder-label alias
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
# Long-command channel — how the agent runs a command that would exceed the 10-min per-call limit.
RUNCHAN_LINE="LONG COMMANDS (>10 min): any command you run yourself in your own shell is force-killed after 10 minutes. If you need to run ANY command that may take longer — a slow build, a long audit/check, anything — do NOT run it yourself. Instead END your turn with (and put NOTHING after) a block in EXACTLY this shape: a line '<<<RUN cwd=RELPATH>>>' where RELPATH is a directory INSIDE this repo relative to the repo root (usually 'LeanEuclidPlus'), then the command on its own line(s), then a line '<<<END>>>'. This is NOT giving up or stopping — the experiment runner just runs that command with NO time limit while you sit idle, then resumes you with its full output so you can keep working. Use it ONLY for genuinely long commands; run short ones normally."

if [ "$MODE" = mymethod ]; then
  # --my-method: verbatim operator-guide "Full" prompt + the two completion signals.
  PROMPT="Prove LeanEuclidPlus/$rel/Main.lean end to end using /faithful-prove skill. As usual make sure --all passes, and please also wire it at the end. IMPORTANT: run the final 'scripts/check_step.py $rel --all' audit — and any 'check_step.py … --subtree' / '--drive' that will run long — through the long-command <<<RUN>>> channel described below (end your turn with the block and let the runner execute it); do NOT run them yourself in the background and then poll or 'wait for a completion notification', which wastes tokens every turn and will not reliably resume you here. DO NOT read anything OUTSIDE this repository ($REPO), and DO NOT read anything under $REPO/reproducable_experiments/ (that is the experiment harness / eval). Doing either DISQUALIFIES the attempt — AUTO-FAILED. No gaming the eval. Also do NOT use git in ANY way — no 'git' command at all, whether directly or via cd/&&/;/|/a subshell/an absolute path/any wrapper. ANY git use DISQUALIFIES the attempt — AUTO-FAILED. $CERT_LINE $GIVEUP_LINE $RUNCHAN_LINE"
else
  # --ablated: operator-guide "Ablated" prompt + REQUIRED per-sentence backing-file structure (so the
  # skill-less arm produces the same decomposition the eval now checks) + the two completion signals.
  PROMPT="Prove LeanEuclidPlus/$rel/Main.lean — fill every ':= by sorry' so it builds with ZERO sorry. Do NOT change the theorem statement, the '(stepN : …)' claim types, or the '-- @assumption (…)' lines. Also anything euclid cites, must be cited as well in Lean. Note that the venv is at ~/.venvs/euclid/bin/activate for z3 and cvc5. REQUIRED STRUCTURE (this is checked — do NOT prove any sentence inline): for each 'euclid_sentence \"…\" (stepK : CLAIM) := by sorry', (1) create a new file LeanEuclidPlus/$rel/stepK.lean holding ONE lemma 'theorem helper_${BOOK}_${PROPNUM}_stepK (…binders…) : CLAIM := by …' that proves that step (euclid_finish is fine INSIDE the helper), taking whatever facts it needs as hypotheses; (2) add 'import Book${BOOK}.Prop${NN}.stepK' at the top of Main.lean; (3) make Main's body delegate, supplying EVERY hypothesis via euclid_assumption with its type shown — EXACTLY '(by euclid_assumption \"TEXT\" (show TYPE; assumption))', NEVER a bare '(by assumption)'. If a hypothesis has a '-- @assumption (\"NL-TEXT\", TYPE)' line above the sentence, use that NL-TEXT verbatim as the string (so it is clear WHERE that cited fact is used); for the other hypotheses use the empty string \"\". Schematic: in Main '(stepK : CLAIM) := by euclid_apply (helper_${BOOK}_${PROPNUM}_stepK o1 o2 (by euclid_assumption \"the exact @assumption text\" (show TYPE1; assumption)) (by euclid_assumption \"\" (show TYPE2; assumption)))', and in stepK.lean 'theorem helper_${BOOK}_${PROPNUM}_stepK (o1 …) (h1 : TYPE1) (h2 : TYPE2) : CLAIM := by euclid_finish'. DO NOT read anything OUTSIDE this repository ($REPO), and DO NOT read anything under $REPO/reproducable_experiments/ (that is the experiment harness / eval). Doing either DISQUALIFIES the attempt — AUTO-FAILED. No gaming the eval. Also do NOT use git in ANY way — no 'git' command at all, whether directly or via cd/&&/;/|/a subshell/an absolute path/any wrapper. ANY git use DISQUALIFIES the attempt — AUTO-FAILED. $CERT_LINE $GIVEUP_LINE $RUNCHAN_LINE"
fi

# Sent on EVERY resume turn — the headless stand-in for the human re-nudging a
# stalled interactive session (the "I did 60%, continue?" case). It forbids
# stopping unless the turn ends with one of the two exact terminal lines.
CONTINUE_PROMPT="Continue working on the task. You are NOT allowed to stop, pause, or ask for confirmation or permission. The ONLY ways you may end your turn are to output, on its own line: (1) DONE — \"$CERT_STRING\", (2) GIVE UP — \"$GIVEUP_STRING\", or (3) a long-command request block '<<<RUN cwd=…>>> … <<<END>>>' (the runner will execute it with no time limit and resume you with its output). Being slow or taking many steps is NOT a reason to give up — only give up if there is no viable path forward and continuing would just waste time and money. Until you do one of those three things, keep working on your own."

# ============================================================================
# GATE 1 — branch guard: this worktree must be on the arm's branch.
# ============================================================================
branch="$(git -C "$REPO" rev-parse --abbrev-ref HEAD)"
[ "$branch" = "$WANT_BRANCH" ] || {
  echo "ABORT: --$MODE must run on '$WANT_BRANCH', but this worktree is on '$branch'."
  echo "       cd into the correct worktree (see runner/README.md) and retry."; exit 1; }

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
HB=""; WD=""
trap '[ -n "$HB" ] && kill "$HB" 2>/dev/null; [ -n "$WD" ] && kill -KILL "$WD" 2>/dev/null' EXIT

# ============================================================================
# GRADE (identical for both arms): 0 sorry + faithful (texts/citations/structure) + per-sentence
# backing lemma + signature unchanged + claim/@assumption types unchanged + compiles ≤1h. Run ONCE at
# the end, never fed back to the agent (no oracle).
# NOTE: check_faithful stays --relaxed (drops the methodology-only bulk-tactic ban + assumption tag
# gate — we do NOT force assumption structure). The ONE extra faithfulness criterion held equal for
# both arms is the per-sentence backing lemma (check_backing.py); the full method auto-satisfies it.
# ============================================================================
# GRADE — runs the 6 gate checks. Sets the global GRADE_FAIL to the name of the FIRST failing check
# ("" when all pass), and TEES the full stdout+stderr of every check to $OUT/grade.log so a FAIL's
# EXACT cause is always recoverable from the run folder (nothing is discarded to /dev/null anymore).
grade() {
  local glog="$OUT/grade.log"
  GRADE_FAIL=""
  { echo "===== GRADE $(date '+%F %T') · $rel · arm=$MODE · node=$(hostname 2>/dev/null) ====="
    echo "worktree: $LEP"; echo; } > "$glog"

  [ -f "$main" ] || { GRADE_FAIL="main_missing"; echo "FAIL: $main does not exist" >> "$glog"; return 1; }

  local sc; sc=$(grep -c 'sorry' "$main")
  { echo "----- [sorry_count] -----"; echo "sorry count = $sc  (must be 0)"; echo; } >> "$glog"
  [ "$sc" -eq 0 ] || { GRADE_FAIL="sorry(count=$sc)"; echo "FAIL: found $sc 'sorry' in Main" >> "$glog"; return 1; }

  echo "----- [check_faithful] -----" >> "$glog"
  ( cd "$LEP" && python3 scripts/check_faithful.py  --relaxed "$rel/Main.lean" ) >> "$glog" 2>&1 \
    || { GRADE_FAIL="check_faithful";   echo ">>> check_faithful FAILED"   >> "$glog"; return 1; }
  echo "----- [check_backing] -----" >> "$glog"
  ( cd "$LEP" && python3 scripts/check_backing.py            "$rel/Main.lean" ) >> "$glog" 2>&1 \
    || { GRADE_FAIL="check_backing";    echo ">>> check_backing FAILED"    >> "$glog"; return 1; }
  echo "----- [check_signatures] -----" >> "$glog"
  ( cd "$LEP" && python3 scripts/check_signatures.py         "$rel/Main.lean" ) >> "$glog" 2>&1 \
    || { GRADE_FAIL="check_signatures"; echo ">>> check_signatures FAILED" >> "$glog"; return 1; }
  echo "----- [check_steps] -----" >> "$glog"
  ( cd "$LEP" && python3 scripts/check_steps.py     --relaxed "$rel/Main.lean" ) >> "$glog" 2>&1 \
    || { GRADE_FAIL="check_steps";      echo ">>> check_steps FAILED"      >> "$glog"; return 1; }
  echo "----- [lake_build: ${rel//\//.}.Main] -----" >> "$glog"
  ( cd "$LEP" && timeout 3600 lake build "${rel//\//.}.Main" ) >> "$glog" 2>&1 \
    || { GRADE_FAIL="lake_build";       echo ">>> lake_build FAILED (nonzero exit or 3600s timeout)" >> "$glog"; return 1; }

  echo "===== ALL CHECKS PASSED =====" >> "$glog"
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
  printf 'prop: %s\nmode: %s\nmodel: %s\nsession_id: %s\ntranscript: %s\ncost_usd: %s\nwall_sec: %s\ncompile_sec: %s\nstop_reason: %s\nresult: %s\nfail_reason: %s\n' \
    "$rel" "$MODE" "$MODEL" "$sid" "$jsonl" "${spent:-0}" "$(awk "BEGIN{print ${wall_ms:-0}/1000}")" "${grade_sec:-<pending>}" "${stop_reason:-<pending>}" "$1" "${GRADE_FAIL:--}" \
    > "$OUT/result.txt"
}

# Run a `claude -p …` call ("$@"), transparently retrying on a subscription usage/rate-limit error so no
# progress is lost. Such a call is NOT counted as a round: we sleep RETRY_SLEEP and re-issue the SAME command
# until a normal (non-usage-limited) result comes back, then return it in global `out`. Each wait bumps
# $OUT/.wall_extra so the 12h watchdog excludes the outage. Retry triggers: a non-zero exit code, OR an
# is_error JSON result whose text names a usage/rate/quota limit (gated on is_error so an agent turn that
# merely MENTIONS "rate limit" in its own output is never mistaken for one). Bounded ultimately by the
# node's SLURM --time wall (2 days).
agent_call() {  # "$@" = the full claude command to run
  local rc is_err extra
  while :; do
    out="$("$@")"; rc=$?
    is_err="$(printf '%s' "$out" | jq -r '.is_error // empty' 2>/dev/null)"
    if [ "$rc" -ne 0 ] || { [ "$is_err" = true ] && \
         printf '%s' "$out" | grep -qiE 'usage limit|rate limit|limit reached|too many requests|(^|[^0-9])429([^0-9]|$)|resets? at|quota'; }; then
      echo "    ($rel: usage/rate limit hit (rc=$rc) — waiting ${RETRY_SLEEP}s then retrying same resume; NOT counted as a round)"
      extra="$(cat "$OUT/.wall_extra" 2>/dev/null)"; case "$extra" in ''|*[!0-9]*) extra=0 ;; esac
      echo $(( extra + RETRY_SLEEP )) > "$OUT/.wall_extra"     # exclude this wait from the 12h wall
      sleep "$RETRY_SLEEP"
      continue
    fi
    break
  done
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
rm -f "$OUT/.wall_extra" 2>/dev/null   # fresh quota-wait accumulator the watchdog adds to its deadline
# ===== GLOBAL 12h WALL — ONE independent watchdog. It has NOTHING to do with the agent loop, the round
# structure, or any RUN command; it just sleeps until t0+12h. If it ever fires it (1) saves the run exactly
# like the manual fixup — copies the transcript, snapshots PropNN, flips result.txt to TIMEOUT — and (2)
# cancels EVERYTHING: it kills the agent + its build first (leaves→root, TERM then KILL), then the driver.
# A normal finish reaps it (after the loop + in the EXIT trap) so it can never fire on a completed run.
_descendants() { local c; for c in $(pgrep -P "$1" 2>/dev/null); do [ "$c" = "$2" ] && continue; echo "$c"; _descendants "$c" "$2"; done; }
DRIVER_PID=$$
( self=$BASHPID
  # Sleep until t0 + WALL_LIMIT + (quota-wait accumulated so far). The deadline is EXTENDABLE, not fixed:
  # each usage-limit wait in the loop adds its seconds to .wall_extra. We sleep the exact remaining time, then
  # re-read .wall_extra — if it grew during the sleep the deadline moved out, so we sleep the delta; else we
  # fire. With NO outage .wall_extra stays 0, so this is a SINGLE sleep firing at EXACTLY t0+limit (unchanged);
  # extra wakeups happen only once per real outage, never on a busy tick.
  while :; do
    extra="$(cat "$OUT/.wall_extra" 2>/dev/null)"; case "$extra" in ''|*[!0-9]*) extra=0 ;; esac
    left=$(( t0 + WALL_LIMIT_SEC + extra - $(date +%s) ))
    [ "$left" -le 0 ] && break
    sleep "$left"
  done
  echo "    (GLOBAL ${WALL_LIMIT_SEC}s wall hit — watchdog: saving TIMEOUT + cancelling the run)"
  kill -STOP "$DRIVER_PID" 2>/dev/null                                          # FREEZE the driver first: it can't start a new turn/build, and can't race our result.txt write
  cp "$jsonl" "$OUT/transcript.jsonl" 2>/dev/null
  cp -r "$LEP/$rel" "$OUT/" 2>/dev/null
  sed -i 's/^result: .*/result: TIMEOUT/; s/^stop_reason: .*/stop_reason: timeout_12h/' "$OUT/result.txt" 2>/dev/null
  pids="$(_descendants "$DRIVER_PID" "$self")"                                  # agent + build subtree (frozen driver still their parent), excluding us
  for p in $(printf '%s\n' $pids | tac); do kill -TERM "$p" 2>/dev/null; done   # leaves first: let claude tear down its own build
  sleep 2
  for p in $pids; do kill -KILL "$p" 2>/dev/null; done                          # force-kill any survivor (z3/cvc5)
  kill -KILL "$DRIVER_PID" 2>/dev/null                                          # kill the frozen driver last
) &
WD=$!
echo "--- $rel: starting (budget=$BUDGET_DISP · 12h global wall · session $sid) ---"
mb=(); [ "$UNLIMITED" = 1 ] || mb=(--max-budget-usd "$remaining")   # cost cap arg — omitted entirely when unlimited
agent_call claude -p "$PROMPT" --model "$MODEL_ID" --session-id "$sid" --permission-mode acceptEdits --output-format json ${mb[@]+"${mb[@]}"}
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
  # Pick the next prompt. If the agent ended its turn with a `<<<RUN cwd=…>>> … <<<END>>>` block, the
  # DRIVER runs that command with NO per-call time cap (the agent is idle meanwhile) and feeds its FULL
  # output back; otherwise the normal CONTINUE_PROMPT. This is the headless stand-in for interactive
  # "launch in background, get woken when done" — the driver is the supervisor that outlives the turn.
  next_prompt="$CONTINUE_PROMPT"
  run_block="$(printf '%s' "$res" | sed -n '/<<<RUN/,/<<<END>>>/p')"
  if printf '%s' "$run_block" | grep -q '<<<RUN' && printf '%s' "$run_block" | grep -q '<<<END>>>'; then
    runcwd="$(printf '%s' "$run_block" | sed -n 's/.*<<<RUN[[:space:]]*cwd=\([^>]*\)>>>.*/\1/p' | head -1)"
    runcmd="$(printf '%s' "$run_block" | sed '1d;$d')"                 # drop the <<<RUN>>> / <<<END>>> lines
    [ -z "$runcwd" ] && runcwd="."
    abscwd="$( cd "$REPO" && cd "$runcwd" 2>/dev/null && pwd -P )" || abscwd=""
    case "$abscwd" in "$REPO"|"$REPO"/*) : ;; *) abscwd="" ;; esac     # must stay inside this worktree
    if [ -n "$abscwd" ]; then
      runlog="$OUT/run$i.log"
      echo "    [RUN request -> $runcwd (<=${RUN_MAX_SEC}s, agent idle): $(printf '%s' "$runcmd" | tr '\n' ' ' | cut -c1-80)...]"
      ( cd "$abscwd" && timeout "$RUN_MAX_SEC" bash -c "$runcmd" ) > "$runlog" 2>&1; rc=$?
      sz=$(wc -c < "$runlog")
      if [ "$sz" -le "$RUN_MAX_BYTES" ]; then                          # feed the WHOLE output (default)
        body="$(cat "$runlog")"
      else                                                            # only trim a runaway log: head+tail
        body="$(head -c $((RUN_MAX_BYTES/2)) "$runlog")
... [middle cut: full output was $sz bytes; showing first & last $((RUN_MAX_BYTES/2)) bytes — see $runlog] ...
$(tail -c $((RUN_MAX_BYTES/2)) "$runlog")"
      fi
      echo "    [RUN done -> exit $rc, ${sz}B output]"
      next_prompt="Output of your requested command (ran in '$runcwd', exit code $rc):
$body

$CONTINUE_PROMPT"
    else
      echo "    [RUN request REFUSED — cwd '$runcwd' outside repo]"
      next_prompt="RUN request REFUSED: cwd '$runcwd' is empty or resolves OUTSIDE the repository ($REPO). You may only run commands inside your worktree. $CONTINUE_PROMPT"
    fi
  fi
  mb=(); [ "$UNLIMITED" = 1 ] || mb=(--max-budget-usd "$remaining")
  agent_call claude -p "$next_prompt" --resume "$sid" --model "$MODEL_ID" --permission-mode acceptEdits --output-format json ${mb[@]+"${mb[@]}"}
  echo "$out" > "$OUT/round$i.json"
done
[ -n "$WD" ] && kill -KILL "$WD" 2>/dev/null; WD=""   # reap the watchdog FIRST so it can't fire during our normal end-code
kill "$HB" 2>/dev/null; HB=""
cp "$jsonl" "$OUT/transcript.jsonl" 2>/dev/null
# Snapshot the produced Prop folder (Main.lean + step*.lean) INTO the run folder — self-contained, and
# it survives the next repeat's reset. Kept for later (controlled) build-time experiments on the artifact.
cp -r "$LEP/$rel" "$OUT/" 2>/dev/null                         # → $OUT/Prop<NN>/

# ---- outcome: git-use ⟹ AUTO-FAIL (overrides all); give-up / 12h-timeout ⟹ NOT complete, no grade;
# anything else ⟹ grade once -- (transcript + PropNN snapshot already copied above, so TIMEOUT lands
# exactly like the manual fixup.)
status=FAIL; grade_sec=0; GRADE_FAIL=""
# GIT LEAK-GUARD — any git use DISQUALIFIES (no gaming the eval), overriding SUCCESS/gaveup/timeout.
# Scans BOTH channels the agent can run commands through: Bash-tool commands (.command) and <<<RUN>>>
# payloads (only the RUN region of assistant text, so prompt/reasoning mentions of "git" don't false-trip).
# Matches a git TOKEN (word-bounded — 'digit'/'legit' don't match); jq decodes \n so cd\ngit is caught too.
# Any hit ⇒ GRADE_FAIL=git_used + the raw offending commands teed to grade.log (same trace as the checks).
git_hits="$( { jq -r '.. | .command? // empty' "$OUT/transcript.jsonl" 2>/dev/null
               jq -r '.. | .text? // empty'    "$OUT/transcript.jsonl" 2>/dev/null | sed -n '/<<<RUN/,/<<<END>>>/p'
             } | grep -nE '(^|[^A-Za-z0-9_])git([^A-Za-z0-9_]|$)' )"
if [ -n "$git_hits" ]; then
  status=FAIL; GRADE_FAIL="git_used"
  echo "    (AUTO-FAIL: agent used git — DISQUALIFIED, grade skipped; offenders in $OUT/grade.log)"
  { echo "===== GIT LEAK-GUARD TRIPPED $(date '+%F %T') · $rel · arm=$MODE ====="
    echo "AUTO-FAIL: the agent ran git. ANY git use disqualifies the attempt (no gaming the eval)."
    echo "--- offending executed commands (transcript-line : command) ---"
    printf '%s\n' "$git_hits"; } > "$OUT/grade.log"
elif [ "$stop_reason" = gaveup ]; then
  status=GAVEUP; GRADE_FAIL="agent_gaveup"
  echo "    (agent gave up — marked NOT complete, grade skipped)"
elif [ "$stop_reason" = timeout_12h ]; then
  status=TIMEOUT; GRADE_FAIL="wall_timeout_12h"
  echo "    (12h wall limit — marked TIMEOUT, grade skipped)"
else
  gt=$(date +%s)
  grade && status=SUCCESS
  grade_sec=$(( $(date +%s) - gt ))
fi
write_result "$status"
echo "=== $rel -> $status  (stop=$stop_reason · \$$spent · $(( ($(date +%s)-t0)/60 ))m wall · compile ${grade_sec}s${GRADE_FAIL:+ · fail=$GRADE_FAIL}) · grade.log in $OUT ==="
[ "$status" = SUCCESS ]

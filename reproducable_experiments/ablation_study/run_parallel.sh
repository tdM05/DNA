#!/usr/bin/env bash
# ============================================================================
# PARALLEL launcher — run several props at once, one agent per prop, each its
# own model. Prop folders are isolated so agents barely conflict; THIS wrapper
# owns the shared state: hide memory ONCE, install the git leak-guard ONCE,
# restore ONCE on exit, and drive one RB_CHILD run_baseline.sh per job.
# Two jobs on the SAME Book/Prop are REFUSED (same folder = direct conflict).
#
# Usage:
#   bash run_parallel.sh --ablated|--full [--budget 50] MODEL:B.P MODEL:B.P ...
#     MODEL:B.P  = model + Book.Prop, e.g.  opus:2.4  sonnet:3.33  haiku:1.26
# e.g.
#   bash run_parallel.sh --ablated --budget 50 sonnet:2.4 opus:3.33 opus:2.10 opus:1.26 opus:1.47 opus:2.8
#
# Watch:  tail -F reproducable_experiments/ablation_study/out/<mode>/_current.txt   (one line per prop)
# ============================================================================
set -uo pipefail
unset ANTHROPIC_API_KEY
set +u; source "$HOME/.venvs/leaneuclid/bin/activate"; set -u   # z3/cvc5 on PATH for lake build

REPO="$(cd "$(dirname "$0")/../.." && pwd -P)"
ABL="$REPO/reproducable_experiments/ablation_study"
SLUG="$(echo "$REPO" | sed 's#/#-#g')"
MEMDIR="$HOME/.claude/projects/${SLUG}/memory"
HIDDEN="${MEMDIR}.HIDDEN_baseline"
RB="$ABL/run_baseline.sh"

# ---- args ----
MODE=""; BUDGET=50.00; JOBS=()
while [ $# -gt 0 ]; do
  case "$1" in
    --ablated) MODE=ablated ;;
    --full)    MODE=full ;;
    --budget)  BUDGET="${2:?}"; shift ;;
    -*)        echo "unknown flag: $1"; exit 1 ;;
    *)         JOBS+=("$1") ;;
  esac; shift
done
[ -z "$MODE" ]        && { echo "usage: run_parallel.sh --ablated|--full [--budget N] MODEL:B.P ..."; exit 1; }
[ ${#JOBS[@]} -eq 0 ] && { echo "no jobs given — want tokens like  opus:2.4  sonnet:3.33"; exit 1; }

# ---- branch guard (mirror run_baseline) ----
branch="$(git -C "$REPO" rev-parse --abbrev-ref HEAD)"
[ "$MODE" = ablated ] && want=ablation_branch || want=full_methodology_branch
[ "$branch" = "$want" ] || { echo "ABORT: --$MODE must run on '$want' (currently on '$branch')"; exit 1; }

# ---- parse + dedup jobs (refuse the same Book/Prop twice — same folder can't run in parallel) ----
declare -A seen; declare -a J_M J_B J_P
for tok in "${JOBS[@]}"; do
  case "$tok" in *:*.*) : ;; *) echo "bad job token '$tok' — want MODEL:B.P (e.g. opus:2.4)"; exit 1 ;; esac
  model="${tok%%:*}"; bp="${tok#*:}"; book="${bp%%.*}"; prop="${bp#*.}"
  key="$book.$prop"
  [ -n "${seen[$key]:-}" ] && { echo "CONFLICT: Book$book/Prop$prop given twice (${seen[$key]} and $model) — same folder, cannot run both in parallel. Pick ONE model for it."; exit 1; }
  seen[$key]="$model"; J_M+=("$model"); J_B+=("$book"); J_P+=("$prop")
done

OUT="$ABL/out/$MODE"; mkdir -p "$OUT"

# ---- leak-guard ONCE (idempotent; deny ALL git for the agent so it can't git-show the proof) ----
python3 - "$REPO/.claude/settings.json" <<'PY'
import sys
p = sys.argv[1]
try: s = open(p).read()
except FileNotFoundError: print("!! no %s — skipping git leak-guard" % p); sys.exit(0)
rules = ('"Bash(git:*)"', '"Bash(git)"',                                  # deny git (history has the proofs)
         '"Read(**/ablation_study/**)"', '"Edit(**/ablation_study/**)"', '"Write(**/ablation_study/**)"')  # + OTHER runs' results (TOOLS only; see bash hook for full coverage)
need = [r for r in rules if r not in s]
if not need: print("[leak-guard: git + results-folder already denied for agent]"); sys.exit(0)
i = s.index('"deny": [') + len('"deny": [')
block = "".join('\n      %s,' % r for r in need)
if s[i:].lstrip().startswith(']'): block = block.rstrip(',')   # empty deny array → no trailing comma
s = s[:i] + block + s[i:]
open(p, "w").write(s); print("[leak-guard: denied for agent -> %s]" % ", ".join(need))
PY

# ---- hide memory ONCE (both arms) + restore on any exit ----
restore_all() {
  if [ -d "$HIDDEN" ]; then
    [ -d "$MEMDIR" ] && mv "$MEMDIR" "${MEMDIR}.recreated_junk_$$"
    mv "$HIDDEN" "$MEMDIR" && echo "[memory restored]"
  fi
}
trap restore_all EXIT   # normal exit, Ctrl-C, kill — memory always comes back
if [ -d "$MEMDIR" ]; then mv "$MEMDIR" "$HIDDEN" && echo "[memory hidden — both arms]"
else [ -d "$HIDDEN" ] || { echo "!! memory dir not found ($MEMDIR) and none hidden — aborting"; exit 1; }; fi

# ---- launch all jobs in parallel (RB_CHILD ⟹ each child skips its own hide/leak-guard/restore) ----
rm -rf "$OUT/_current.d"; mkdir -p "$OUT/_current.d"
echo "=== launching ${#J_M[@]} parallel jobs (mode=$MODE, branch=$branch, \$$BUDGET each) ==="
pids=()
for i in "${!J_M[@]}"; do
  pp=$(printf '%02d' "${J_P[$i]}"); lbl="Book${J_B[$i]}_Prop${pp}_${J_M[$i]}"
  echo "  · Book${J_B[$i]}/Prop$pp on ${J_M[$i]}  → out/$MODE/$lbl/"
  RB_CHILD=1 bash "$RB" --"$MODE" --book "${J_B[$i]}" --prop "${J_P[$i]}" --model "${J_M[$i]}" --budget "$BUDGET" \
    > "$OUT/$lbl.launchlog" 2>&1 &
  pids+=("$!")
done
echo
echo "=== ${#pids[@]} jobs running. Dashboard (one line per prop):  tail -F $OUT/_current.txt ==="
echo "    per-job result:  $OUT/<label>/result.txt   ·   raw log:  $OUT/<label>.launchlog"
wait
echo
echo "=== all ${#pids[@]} jobs finished — final dashboard: ==="
cat "$OUT/_current.txt" 2>/dev/null

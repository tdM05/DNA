#!/usr/bin/env bash
#SBATCH --partition=cpunodes
#SBATCH --nodes=1
#SBATCH --exclusive
#SBATCH --mem=0
#SBATCH --time=1-00:00:00
#SBATCH --job-name=euclid_pilot
#SBATCH --output=/h/56/taddmao/code/autoform/methodology_compare_worktrees/full/reproducable_experiments/ablation_study/slurm_logs/%x-%j.out
# ============================================================================
# PILOT — pack a few runs onto ONE exclusive node to OBSERVE how much memory
# they commit and whether the shared-.lake builds contend. Pure launch + log,
# no guarding. Bake the list below and just `sbatch pilot.sbatch` (no args).
#
# PREREQ — reset each prop to its map FIRST (the driver only verifies, GATE 3):
#   my-method map = be22807, ablated map = 3d8e371.  For each prop NN:
#     git -C <worktree> show <MAP>:LeanEuclidPlus/Book1/PropNN/Main.lean > <worktree>/LeanEuclidPlus/Book1/PropNN/Main.lean
#     find <worktree>/LeanEuclidPlus/Book1/PropNN -type f ! -name Main.lean -delete
# ============================================================================
set -uo pipefail

# ---- EDIT: what to pack onto this one node ---------------------------------
ARM="my-method"          # my-method | ablated
BOOK=1
PROPS=(1)                # start with ONE for a clean single-agent baseline; add more (e.g. 1 2 3) to pack
BUDGET=-1                # unlimited

# ---- paths -----------------------------------------------------------------
case "$ARM" in
  my-method) WT="/h/56/taddmao/code/autoform/methodology_compare_worktrees/full" ;;
  ablated)   WT="/h/56/taddmao/code/autoform/methodology_compare_worktrees/ablated" ;;
  *) echo "bad ARM '$ARM'"; exit 1 ;;
esac
DRIVER="$WT/reproducable_experiments/ablation_study/run_comparison_experiment.sh"
LOGDIR="$WT/reproducable_experiments/ablation_study/slurm_logs"
mkdir -p "$LOGDIR"
MEMLOG="$LOGDIR/mem-${SLURM_JOB_ID:-local}.log"

echo "=== $(date) · node=$(hostname) · arm=$ARM · Book$BOOK props=${PROPS[*]} · budget=$BUDGET ==="
echo "per-run logs -> $LOGDIR/run_*.log ; memory samples -> $MEMLOG"

# ---- background memory sampler (OBSERVE ONLY — logs, never gates/kills) -----
( while :; do
    c=$(grep -m1 Committed_AS /proc/meminfo | tr -dc '0-9')
    l=$(grep -m1 CommitLimit  /proc/meminfo | tr -dc '0-9')
    a=$(grep -m1 MemAvailable /proc/meminfo | tr -dc '0-9')
    n=$(pgrep -u "$USER" -fc 'claude' 2>/dev/null || echo 0)
    printf '%s  Committed_AS=%dG / CommitLimit=%dG  MemAvail=%dG  claude_procs=%s\n' \
      "$(date +%H:%M:%S)" $((c/1024/1024)) $((l/1024/1024)) $((a/1024/1024)) "$n" >> "$MEMLOG"
    sleep 30
  done ) &
SAMPLER=$!
trap 'kill "$SAMPLER" 2>/dev/null' EXIT

# ---- launch each run backgrounded, one log file each -----------------------
pids=()
for p in "${PROPS[@]}"; do
  echo "launching $ARM Book$BOOK/Prop$p"
  bash "$DRIVER" --"$ARM" --book "$BOOK" --prop "$p" --budget "$BUDGET" \
    > "$LOGDIR/run_Book${BOOK}_Prop${p}.log" 2>&1 &
  pids+=("$!")
done
wait "${pids[@]}"
echo "=== all ${#pids[@]} runs done · $(date) ==="

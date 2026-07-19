#!/usr/bin/env bash
#SBATCH --partition=cpunodes
#SBATCH --nodes=1
#SBATCH --exclusive
#SBATCH --mem=0
#SBATCH --time=1-00:00:00
#SBATCH --job-name=euclid
#SBATCH --output=/h/56/taddmao/code/autoform/DNA/reproducable_experiments/ablation_study/out/slurm_logs/%x-%A_%a.out
# ============================================================================
# WORKER — do NOT run or edit this directly. `submit.sh` sets the knobs
# (ARM/BOOK/PROPS/REPEATS/BUDGET, passed in via --export) and submits it as a
# job array. ONE array task = one prop = PROPS[$SLURM_ARRAY_TASK_ID] = one
# exclusive node; the task runs that prop's REPEATS sequentially on that node.
# ============================================================================
set -uo pipefail
: "${ARM:?run via: bash submit.sh  (do not sbatch this directly)}"
: "${BOOK:?}" "${PROPS:?}" "${REPEATS:?}" "${BUDGET:?}" "${SLURM_ARRAY_TASK_ID:?}"
read -r -a PROPS <<< "$PROPS"                    # space-separated string → array
N=${#PROPS[@]}
[ "$SLURM_ARRAY_TASK_ID" -ge "$N" ] && { echo "no task $SLURM_ARRAY_TASK_ID — only $N props"; exit 0; }
PROP="${PROPS[$SLURM_ARRAY_TASK_ID]}"

ROOT="/h/56/taddmao/code/autoform/methodology_compare_worktrees"
OUT_BASE="/h/56/taddmao/code/autoform/DNA/reproducable_experiments/ablation_study/out"
case "$ARM" in
  my-method) WT="$ROOT/full";    MAP="be22807" ;;
  ablated)   WT="$ROOT/ablated"; MAP="3d8e371" ;;
  *) echo "bad ARM '$ARM'"; exit 1 ;;
esac
DRIVER="$WT/reproducable_experiments/ablation_study/run_comparison_experiment.sh"
LOGDIR="$OUT_BASE/slurm_logs"; mkdir -p "$LOGDIR"
NN="$(printf '%02d' "$PROP")"
PROPDIR="$WT/LeanEuclidPlus/Book${BOOK}/Prop${NN}"
MEMLOG="$LOGDIR/mem-${SLURM_ARRAY_JOB_ID}_${SLURM_ARRAY_TASK_ID}.log"

echo "=== $(date) · node=$(hostname) · task=$SLURM_ARRAY_TASK_ID · $ARM Book${BOOK}/Prop${PROP} · $REPEATS repeats ==="

# memory sampler (observe only — logs commit level, never gates/kills)
( while :; do
    c=$(grep -m1 Committed_AS /proc/meminfo | tr -dc '0-9'); l=$(grep -m1 CommitLimit /proc/meminfo | tr -dc '0-9')
    printf '%s  Committed_AS=%dG / CommitLimit=%dG\n' "$(date +%H:%M:%S)" $((c/1024/1024)) $((l/1024/1024)) >> "$MEMLOG"
    sleep 30
  done ) &
SAMPLER=$!; trap 'kill "$SAMPLER" 2>/dev/null' EXIT

for r in $(seq 1 "$REPEATS"); do
  echo "--- repeat $r/$REPEATS: reset Prop${NN} to map $MAP, then run ---"
  git -C "$WT" show "$MAP:LeanEuclidPlus/Book${BOOK}/Prop${NN}/Main.lean" > "$PROPDIR/Main.lean" \
    || { echo "ABORT repeat $r: cannot read map"; continue; }
  find "$PROPDIR" -type f ! -name Main.lean -delete
  bash "$DRIVER" --"$ARM" --book "$BOOK" --prop "$PROP" --budget "$BUDGET" || true
done
echo "=== $(date) · task $SLURM_ARRAY_TASK_ID done ($ARM Book${BOOK}/Prop${PROP}) ==="

#!/usr/bin/env bash
#SBATCH --partition=cpunodes
#SBATCH --nodes=1
#SBATCH --exclusive
#SBATCH --mem=0
#SBATCH --time=2-00:00:00
#SBATCH --job-name=oracle
#SBATCH --output=/h/56/taddmao/code/autoform/DNA/reproducable_experiments/oracle_experiment/out/slurm_logs/%x-%A_%a.out
# ============================================================================
# WORKER — do NOT sbatch directly; run `bash submit.sh`. ONE array task = one prop
# (= PROPS[$TASK_ID]) = one exclusive node, running REPEATS sequentially.
# Ablation design: ALL tasks share the ONE llm_oracle worktree (already built) — the
# driver runs in it directly, no per-task worktree, no .lake copy. Different props are
# different folders so they don't clobber; the driver resets only its own prop folder.
# ============================================================================
set -uo pipefail
: "${PROPS:?run via: bash submit.sh}" "${BUDGET:?}" "${MODEL:?}" "${MAX_MAP_ROUNDS:?}" "${REPEATS:?}" "${DRIVER:?}" "${SLURM_ARRAY_TASK_ID:?}"
read -r -a PROPS <<< "$PROPS"
N=${#PROPS[@]}
[ "$SLURM_ARRAY_TASK_ID" -ge "$N" ] && { echo "no task $SLURM_ARRAY_TASK_ID — only $N props"; exit 0; }
entry="${PROPS[$SLURM_ARRAY_TASK_ID]}"                       # e.g. Book3/Prop11
BOOK="$(printf '%s' "$entry" | sed -n 's#Book\([0-9]\+\)/Prop.*#\1#p')"
PROP="$(printf '%s' "$entry" | sed -n 's#Book[0-9]\+/Prop0*\([0-9]\+\)#\1#p')"
[ -n "$BOOK" ] && [ -n "$PROP" ] || { echo "bad prop entry '$entry'"; exit 1; }

echo "=== $(date) · node=$(hostname) · task=$SLURM_ARRAY_TASK_ID · $entry · $REPEATS repeat(s) ==="
for r in $(seq 1 "$REPEATS"); do
  echo "--- repeat $r/$REPEATS: $entry (shared llm_oracle worktree; driver auto-resets this prop) ---"
  bash "$DRIVER" --book "$BOOK" --prop "$PROP" --budget "$BUDGET" --model "$MODEL" --max-map-rounds "$MAX_MAP_ROUNDS" || true
done
echo "=== $(date) · task $SLURM_ARRAY_TASK_ID done ($entry) ==="

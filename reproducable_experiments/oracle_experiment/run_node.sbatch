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
#
# PARALLEL ISOLATION: the task runs in its OWN per-task git worktree (detached at
# llm_oracle_branch) with a copied-warm .lake. This isolates .lake, .claude/settings.json,
# scripts/step_signatures.json and scripts/assumption_tags.json — the shared state that
# would otherwise race across concurrent props (NFS file-locks don't work across nodes).
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

BASE_WT="/h/56/taddmao/code/autoform/methodology_compare_worktrees/llm_oracle"
WT_PARENT="/h/56/taddmao/code/autoform/methodology_compare_worktrees/_oracle_runs"
RUN_WT="$WT_PARENT/run_${SLURM_ARRAY_JOB_ID}_${SLURM_ARRAY_TASK_ID}"
mkdir -p "$WT_PARENT"

echo "=== $(date) · node=$(hostname) · task=$SLURM_ARRAY_TASK_ID · $entry · $REPEATS repeat(s) ==="

# ---- create the per-task worktree (detached at the branch commit) ----
git -C "$BASE_WT" worktree prune 2>/dev/null || true
if ! git -C "$BASE_WT" worktree add --detach "$RUN_WT" llm_oracle_branch; then
  echo "ABORT: could not create per-task worktree $RUN_WT"; exit 1
fi
# tear it down on ANY exit (success, failure, scancel)
cleanup() { cd /; git -C "$BASE_WT" worktree remove --force "$RUN_WT" 2>/dev/null || rm -rf "$RUN_WT"; git -C "$BASE_WT" worktree prune 2>/dev/null || true; }
trap cleanup EXIT

# ---- copy the warm build so this task doesn't rebuild SystemE/mathlib (or race the base) ----
echo "--- copying warm .lake into the per-task worktree (one-time) ---"
cp -a "$BASE_WT/LeanEuclidPlus/.lake" "$RUN_WT/LeanEuclidPlus/.lake" || { echo "ABORT: .lake copy failed"; exit 1; }

export WORKTREE_OVERRIDE="$RUN_WT"
for r in $(seq 1 "$REPEATS"); do
  echo "--- repeat $r/$REPEATS: $entry (isolated worktree $RUN_WT; driver auto-resets to blank) ---"
  bash "$DRIVER" --book "$BOOK" --prop "$PROP" --budget "$BUDGET" --model "$MODEL" --max-map-rounds "$MAX_MAP_ROUNDS" || true
done
echo "=== $(date) · task $SLURM_ARRAY_TASK_ID done ($entry) ==="

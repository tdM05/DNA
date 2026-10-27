#!/usr/bin/env bash
# ============================================================================
# THE launcher — edit the KNOBS below, then:  bash submit.sh
# It counts PROPS, derives the job-array range itself, and submits — you never
# type --array. One prop per exclusive node; REPEATS sequential per node.
# (props.txt is just a reference list of the 15 ablation props.)
# ============================================================================
set -euo pipefail

# ---- KNOBS (the only thing you edit) ---------------------------------------
export PROPS="Book1/Prop03"       # props to run, space-separated: e.g. "Book3/Prop11 Book2/Prop03 Book1/Prop06"
export BUDGET=-1                  # -1 = unlimited; or e.g. 100.00
export MODEL=opus
export MAX_MAP_ROUNDS=10          # max oracle map reject/revise rounds before MAP_NOCONVERGE
export REPEATS=1                  # runs per prop (sequential on its node)
THROTTLE=5                        # max nodes running at once
WARM=1                            # 1 = warm the base build before submitting; 0 = skip

# ---- submit (range derived from PROPS — no manual --array) ------------------
HERE="$(cd "$(dirname "$0")" && pwd -P)"
export DRIVER="$HERE/run_oracle_experiment.sh"
WORKTREE="/h/56/taddmao/code/autoform/methodology_compare_worktrees/llm_oracle"
LEP="$WORKTREE/LeanEuclidPlus"
mkdir -p "$HERE/out/slurm_logs"

N=$(echo "$PROPS" | wc -w)
[ "$N" -gt 0 ] || { echo "set PROPS in submit.sh"; exit 1; }

br="$(git -C "$WORKTREE" rev-parse --abbrev-ref HEAD)"
[ "$br" = "llm_oracle_branch" ] || { echo "ABORT: $WORKTREE is on '$br', expected llm_oracle_branch"; exit 1; }

if [ "$WARM" = 1 ]; then
  echo "[warm] building base .lake once (each per-task worktree copies it; set WARM=0 to skip)"
  ( set +u; source "$HOME/.venvs/leaneuclid/bin/activate" 2>/dev/null; set -u
    . "$HOME/.elan/env" 2>/dev/null || export PATH="$HOME/.elan/bin:$PATH"
    cd "$LEP" && lake build Book1 Book2 Book3 ) || echo "  (nonzero — sorry warnings on the blank corpus are expected)"
fi

echo "arm=llm-oracle · $N prop(s) [$PROPS] · $REPEATS repeat(s) · <=$THROTTLE nodes at once · budget=$BUDGET · max_map_rounds=$MAX_MAP_ROUNDS"
echo "-> sbatch --array=0-$((N-1))%$THROTTLE run_node.sbatch"
sbatch --export=ALL --array=0-$((N-1))%"$THROTTLE" "$HERE/run_node.sbatch"

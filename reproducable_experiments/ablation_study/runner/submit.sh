#!/usr/bin/env bash
# ============================================================================
# THE launcher — the ONLY file you edit + run.  Usage:  bash submit.sh
# Edit the knobs below and run it. It counts PROPS, derives the job-array range
# itself, and submits — you NEVER type --array, so the count can't mismatch.
# One prop per node; each node runs that prop's REPEATS sequentially.
# Run ONE arm, then flip ARM and run again for the other.
# ============================================================================
set -euo pipefail

# ---- KNOBS (the only thing you change) -------------------------------------
export ARM="ablated"     # my-method | ablated
export BOOK=2
export PROPS="3 12"   # the props to run
export REPEATS=2           # runs per prop (sequential on its node)
export BUDGET=-1           # -1 = unlimited
THROTTLE=5                 # max array tasks running AT ONCE (jobs now pack onto shared nodes)

# ---- submit (range derived from PROPS — no manual --array) ------------------
N=$(echo "$PROPS" | wc -w)
HERE="$(cd "$(dirname "$0")" && pwd -P)"
echo "arm=$ARM · $N props · $REPEATS repeats each · <=$THROTTLE nodes at once"
echo "-> sbatch --array=0-$((N-1))%$THROTTLE run_node.sbatch"
sbatch --export=ALL --array=0-$((N-1))%"$THROTTLE" "$HERE/run_node.sbatch"

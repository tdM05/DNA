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
export BOOK=1
export PROPS="18"   # the props to run
export REPEATS=1           # runs per prop (sequential on its node)
export BUDGET=-1           # -1 = unlimited
THROTTLE=1                 # max nodes running AT ONCE (the rest queue)

# ---- submit (range derived from PROPS — no manual --array) ------------------
N=$(echo "$PROPS" | wc -w)
HERE="$(cd "$(dirname "$0")" && pwd -P)"
echo "arm=$ARM · $N props · $REPEATS repeats each · <=$THROTTLE nodes at once"
echo "-> sbatch --array=0-$((N-1))%$THROTTLE run_node.sbatch"
sbatch --export=ALL --array=0-$((N-1))%"$THROTTLE" "$HERE/run_node.sbatch"

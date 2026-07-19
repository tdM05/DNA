#!/usr/bin/env bash
#SBATCH --partition=cpunodes
#SBATCH --nodes=1
#SBATCH --exclusive
#SBATCH --mem=0
#SBATCH --time=1-00:00:00
#SBATCH --job-name=euclid
#SBATCH --output=/h/56/taddmao/code/autoform/DNA/reproducable_experiments/ablation_study/out/slurm_logs/%x-%j.out
# ============================================================================
# ONE node runs a chosen set of props for ONE arm. Edit the CONFIG, `sbatch` it,
# and it grabs a node and runs those props. Want more? Edit PROPS (or ARM) and
# `sbatch` again → another node. You control what packs onto each node.
#
# Per node: each prop is a background worker that runs its REPEATS *sequentially*
# (resetting the prop to its map between repeats); the props run in PARALLEL. So
# the SAME prop never overlaps itself (shared-worktree safe), but different props
# do. A memory sampler logs Committed_AS to the out dir (observe only — no guard).
# Results (result.txt + transcript + turns + the produced PropNN/ artifact) go to
# the CENTRAL out dir, one folder per run.
# ============================================================================
set -uo pipefail

# ---- CONFIG (edit here) ----------------------------------------------------
ARM="my-method"          # my-method | ablated   (one arm per node)
BOOK=1
PROPS=(1)                # props to pack on THIS node; more props = more agents at once
REPEATS=3
BUDGET=-1

# ---- paths (mirror the driver) ---------------------------------------------
ROOT="/h/56/taddmao/code/autoform/methodology_compare_worktrees"
OUT_BASE="/h/56/taddmao/code/autoform/DNA/reproducable_experiments/ablation_study/out"
case "$ARM" in
  my-method) WT="$ROOT/full";    MAP="be22807" ;;
  ablated)   WT="$ROOT/ablated"; MAP="3d8e371" ;;
  *) echo "bad ARM '$ARM'"; exit 1 ;;
esac
DRIVER="$WT/reproducable_experiments/ablation_study/run_comparison_experiment.sh"
LOGDIR="$OUT_BASE/slurm_logs"; mkdir -p "$LOGDIR"
MEMLOG="$LOGDIR/mem-${SLURM_JOB_ID:-local}.log"

echo "=== $(date) · node=$(hostname) · arm=$ARM · Book$BOOK props=${PROPS[*]} · $REPEATS repeats each ==="

# ---- memory sampler (OBSERVE ONLY — logs, never gates/kills) ----------------
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
echo "memory samples -> $MEMLOG"

# ---- one background worker per prop; each does its repeats SEQUENTIALLY ------
worker() {  # $1 = prop
  local p="$1" nn r
  nn="$(printf '%02d' "$p")"
  local propdir="$WT/LeanEuclidPlus/Book${BOOK}/Prop${nn}"
  for r in $(seq 1 "$REPEATS"); do
    echo "[Prop$p] repeat $r/$REPEATS: reset to map $MAP, then run"
    git -C "$WT" show "$MAP:LeanEuclidPlus/Book${BOOK}/Prop${nn}/Main.lean" > "$propdir/Main.lean" \
      || { echo "[Prop$p] ABORT repeat $r: cannot read map"; continue; }
    find "$propdir" -type f ! -name Main.lean -delete
    bash "$DRIVER" --"$ARM" --book "$BOOK" --prop "$p" --budget "$BUDGET" || true
  done
  echo "[Prop$p] all $REPEATS repeats done"
}

pids=()
for p in "${PROPS[@]}"; do worker "$p" & pids+=("$!"); done
wait "${pids[@]}"
echo "=== $(date) · node done (arm=$ARM, props=${PROPS[*]}) ==="

#!/usr/bin/env bash
# Per-prop compile-time benchmark: naive_llm vs my_method (ordered decomposition).
#
# The two "worlds" live in two git worktrees that share a BYTE-IDENTICAL SystemE
# (verified: diff -rq of the two SystemE trees is empty), so the only thing that
# differs is the PROOF structure:
#   naive = ablated worktree : one monolithic  Book<N>/PropNN/Main.lean
#   mine  = full    worktree : Main.lean + its stepK.lean ordered-decomposition
#           backing files (building Book<N>.PropNN.Main transitively compiles them all).
# Both prove the SAME proposition_N under the SAME lake target Book<N>.PropNN.Main.
#
# Protocol per world (symmetric + clean, mirrors ../compile_time):
#   1. rm -rf <root>/.lake/build   -> wipe all our built oleans (NOT .lake/packages/Mathlib)
#   2. lake build SystemE          -> build the shared framework once, UNTIMED
#   3. time each of the 5 targets cold, ascending, one at a time: timeout $CAP lake build <target>
# Then repeat 1-3 for the other world. SMT is uncapped (systemE.solverTime=100000), so the
# per-target wall cap ($CAP) is the sole cutoff. Repeats NUM_RUNS times; each run writes
# results/run<id>_<stamp>/{naive.csv,mine.csv,build.log,meta.txt} so results accumulate and a
# killed job keeps completed runs.
set -uo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
NAIVE_LAKE="/u/taddmao/code/autoform/methodology_compare_worktrees/ablated/LeanEuclidPlus"
MINE_LAKE="/u/taddmao/code/autoform/methodology_compare_worktrees/full/LeanEuclidPlus"
RESULTS="$HERE/results"
CAP="${CAP:-3600}"; NUM_RUNS="${NUM_RUNS:-5}"; HOST="$(hostname -s)"  # lake uses its default parallelism (this lake has no -j), same as ../compile_time
# The 5 props in question, in ascending build order (same target name in both worlds):
TARGETS=(Book1.Prop01.Main Book1.Prop26.Main Book1.Prop43.Main Book1.Prop47.Main Book3.Prop33.Main)
mkdir -p "$RESULTS"

measure() {  # $1 csv-label  $2 lake-target  $3 outfile   (run from the world's LAKE root; uses $LOGF)
  local name="$1" tgt="$2" out="$3" t0 t1 rc dt st tmp
  tmp="$(mktemp)"
  echo "===== $tgt =====" >> "$LOGF"
  t0=$(date +%s.%N); timeout -k 30 "$CAP" lake build "$tgt" >"$tmp" 2>&1; rc=$?; t1=$(date +%s.%N)
  cat "$tmp" >> "$LOGF"
  dt=$(awk "BEGIN{printf \"%.2f\", $t1-$t0}")
  # Classify by OUTPUT, not exit code. lake returns a NONZERO exit when a freshly-built DEPENDENCY
  # uses `sorry`, yet still prints "Build completed successfully" and produces the olean. RULE: for
  # PropN a `sorry` is allowed ONLY in a cited PropK (K != N); a sorry in PropN's OWN cone (Main or a
  # stepK, i.e. a file under Book*/PropN/) makes it an incomplete proof -> `sorry_self` (invalid).
  # So: timeout -> T.O.; built + no self-sorry -> ok; built + self-sorry -> sorry_self; real error -> fail.
  own="${tgt%%.*}/$(printf '%s' "$tgt" | cut -d. -f2)/"        # Book1.Prop43.Main -> Book1/Prop43/
  if   [ $rc -eq 124 ]; then st="T.O."; dt="$CAP"
  elif grep -q "Build completed successfully" "$tmp"; then
    if grep "declaration uses 'sorry'" "$tmp" | grep -q "$own"; then st=sorry_self; else st=ok; fi
  elif [ $rc -eq 0 ]; then st=ok
  else st=fail; fi
  rm -f "$tmp"
  printf '%s,%s,%s\n' "$name" "$dt" "$st" | tee -a "$out"
  case "$st" in fail|"T.O.") pkill -9 -x z3 2>/dev/null; pkill -9 -x cvc5 2>/dev/null; pkill -9 -x lean 2>/dev/null; sleep 1 ;; esac
  return 0
}

run_world() {  # $1 world-name  $2 LAKE-root  $3 outfile
  local world="$1" root="$2" out="$3"
  echo "  -- world=$world  root=$root" | tee -a "$LOGF"
  cd "$root" || { echo "FATAL: no such root: $root"; exit 1; }
  rm -rf "$root/.lake/build"                                    # clear: wipe this world's oleans
  lake build SystemE >>"$LOGF" 2>&1 || { echo "FATAL: SystemE build failed ($world)"; exit 1; }
  echo "target,wall_s,status" > "$out"
  for tgt in "${TARGETS[@]}"; do measure "$tgt" "$tgt" "$out"; done
}

for run in $(seq 1 "$NUM_RUNS"); do
  STAMP="$(date +%Y%m%d_%H%M%S)"
  RUNDIR="$RESULTS/run${run}_${STAMP}"; mkdir -p "$RUNDIR"
  LOGF="$RUNDIR/build.log"
  { echo "run:   $run/$NUM_RUNS"; echo "host:  $(hostname)"; echo "date:  $(date)";
    echo "cap:   ${CAP}s   jobs: lake-default";
    echo "naive: $NAIVE_LAKE  @ $(git -C "$NAIVE_LAKE" rev-parse HEAD 2>/dev/null)";
    echo "mine:  $MINE_LAKE  @ $(git -C "$MINE_LAKE" rev-parse HEAD 2>/dev/null)";
    echo "props: ${TARGETS[*]}"; } > "$RUNDIR/meta.txt"
  echo "### RUN $run/$NUM_RUNS -> $RUNDIR"

  run_world naive "$NAIVE_LAKE" "$RUNDIR/naive.csv"            # clear -> build SystemE -> time 5 props
  run_world mine  "$MINE_LAKE"  "$RUNDIR/mine.csv"             # clear again -> other method
done
echo "### done: $NUM_RUNS run(s) under $RESULTS"

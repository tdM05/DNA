#!/usr/bin/env bash
# Per-prop compile-time benchmark: faithful Book1 vs original OldBook1.
# Repeats NUM_RUNS times; each run = a clean build per world (rm -rf .lake/build -> lake build SystemE
# -> time each target). Mathlib/external deps in .lake/packages are never wiped. SMT is uncapped
# (SystemE default), so the per-target wall cap ($CAP) is the only cutoff. Each run writes
# results/run<id>_<datetime>/{new.csv,old.csv,build.log,meta.txt}, so results accumulate and a killed
# job keeps completed runs.
set -uo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
LAKE="$(cd "$HERE/../../LeanEuclidF" && pwd)"
RESULTS="$HERE/results"
CAP="${CAP:-3600}"; NUM_RUNS="${NUM_RUNS:-5}"; HOST="$(hostname -s)"
mkdir -p "$RESULTS"; cd "$LAKE"

measure() {  # $1 csv-name  $2 lake-target  $3 outfile   (uses the per-run $LOGF)
  local name="$1" tgt="$2" out="$3" t0 t1 rc dt st
  echo "===== $tgt =====" >> "$LOGF"
  t0=$(date +%s.%N); timeout -k 30 "$CAP" lake build "$tgt" >>"$LOGF" 2>&1; rc=$?; t1=$(date +%s.%N)
  dt=$(awk "BEGIN{printf \"%.2f\", $t1-$t0}")
  if   [ $rc -eq 0   ]; then st=ok
  elif [ $rc -eq 124 ]; then st="T.O."; dt="$CAP"
  else st=fail; fi
  printf '%s,%s,%s\n' "$name" "$dt" "$st" | tee -a "$out"
  [ $rc -ne 0 ] && { pkill -9 -x z3 2>/dev/null; pkill -9 -x cvc5 2>/dev/null; pkill -9 -x lean 2>/dev/null; sleep 1; }
  return 0
}

setup() {  # wipe all our built content, rebuild the shared base SystemE (Mathlib reused from .lake/packages)
  rm -rf "$LAKE/.lake/build"
  lake build SystemE || { echo "FATAL: SystemE build failed"; exit 1; }
}

for run in $(seq 1 "$NUM_RUNS"); do
  STAMP="$(date +%Y%m%d_%H%M%S)"
  RUNDIR="$RESULTS/run${run}_${STAMP}"; mkdir -p "$RUNDIR"
  LOGF="$RUNDIR/build.log"
  { echo "run:  $run/$NUM_RUNS"; echo "host: $(hostname)"; echo "date: $(date)";
    echo "cap:  ${CAP}s"; echo "git:  $(git -C "$HERE" rev-parse HEAD 2>/dev/null)"; } > "$RUNDIR/meta.txt"
  echo "### RUN $run/$NUM_RUNS -> $RUNDIR"

  NEW="$RUNDIR/new.csv"; setup; echo "target,wall_s,status" > "$NEW"
  for n in $(seq -w 1 48); do measure "$n" "Book1.Prop$n.Main" "$NEW"; done

  OLD="$RUNDIR/old.csv"; setup; echo "target,wall_s,status" > "$OLD"
  for n in $(seq -w 1 48); do measure "$n" "OldBook1.Prop$n" "$OLD"; done
done
echo "### done: $NUM_RUNS run(s) under $RESULTS"

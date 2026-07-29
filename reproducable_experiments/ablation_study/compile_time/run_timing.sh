#!/usr/bin/env bash
# Compile-time benchmark of the ABLATION-STUDY proofs: my method vs the ablated (bare-LLM) arm,
# across 3 books of the 15 (Book1/2/3). Each arm generated up to 3 runs per proposition; every run
# that SUCCEEDED produced a zero-sorry, compiling PropNN/ folder. Here we measure, per such proof,
# the wall-clock to compile it cold in the real repo.
#
# Protocol (IDENTICAL for both arms, symmetric):
#   per timing pass, per arm:
#     1. rm -rf .lake/build   — wipe all our built content (SystemE + every Euclid lib). Mathlib in
#        .lake/packages is NOT touched, so it is never rebuilt.
#     2. lake build SystemE   — build the shared framework once (untimed).
#     3. walk the proofs IN ORDER; for each successful run's proof:
#          rm -rf Book<N>/Prop<NN>              (clear the repo's own proof folder)
#          cp -r  <generated PropNN>/  Book<N>/Prop<NN>
#          time: lake build Book<N>.Prop<NN>.Main   (record wall + status)
#          rm -rf Book<N>/Prop<NN> ; git checkout HEAD -- Book<N>/Prop<NN>   (REVERT to the repo proof)
#        Only the ONE target folder is ever swapped; every cited dependency prop is the repo's own,
#        identical across both arms -> the comparison is fair with no special dep handling.
#
# A run that TIMED OUT / FAILED in the ablation study produced NO artifact -> recorded as a `nan`
# row (so the data is COMPLETE: every (arm, prop, run) cell is present). The ablated arm solved only
# a handful of props, so most of its cells are nan by construction.
#
# The whole sweep is repeated NUM_RUNS times (default 3) for compile-noise stability. Each pass
# writes results/pass<id>_<datetime>/{mymethod.csv,ablated.csv,build.log,meta.txt}, so results
# accumulate and a killed job keeps completed passes.
set -uo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO="$(cd "$HERE/../../.." && pwd)"                 # …/DNA
LAKE="$REPO/LeanEuclidPlus"
OUT="$HERE/../out"                                   # ablation_study/out/<arm>/<label>/<run>/PropNN
RESULTS="$HERE/results"
CAP="${CAP:-3600}"; NUM_RUNS="${NUM_RUNS:-3}"; HOST="$(hostname -s)"
ARMS=(mymethod ablated)
mkdir -p "$RESULTS"

# ---- proposition list, in build order (Book, then Prop ascending) ---------------------------------
# label = the out/ folder name; TARGET = the repo path Book<N>/Prop<NN> we swap into.
PROPS=(
  Book1_Prop03 Book1_Prop06 Book1_Prop12 Book1_Prop18 Book1_Prop20
  Book1_Prop27 Book1_Prop30 Book1_Prop36 Book1_Prop45
  Book2_Prop03 Book2_Prop12
  Book3_Prop06 Book3_Prop11 Book3_Prop25 Book3_Prop36
)

# result of an out/ run = SUCCESS / TIMEOUT / … (parsed from result.txt)
run_result() { grep -E '^result:' "$1/result.txt" 2>/dev/null | head -1 | cut -d: -f2- | tr -d ' '; }

measure() {  # $1 csv  $2 arm  $3 label(Book1_Prop06)  $4 run_id  (uses $LOGF; times only the build)
  local out="$1" arm="$2" label="$3" run_id="$4"
  local book="${label%%_*}"; local prop="${label##*_}"          # Book1 / Prop06
  local target="$LAKE/$book/$prop"
  local src="$OUT/$arm/${label}_opus/$run_id/$prop"
  local tgt="${book}.${prop}.Main"
  local t0 t1 rc dt st

  echo "===== $arm $label $run_id -> build $tgt =====" >> "$LOGF"
  if [ ! -d "$src" ] || [ ! -f "$src/Main.lean" ]; then
    echo "  (no artifact — nan)" >> "$LOGF"
    printf '%s,%s,%s,%s,%s\n' "$label" "$run_id" "nan" "nan" "no_artifact" | tee -a "$out"
    return 0
  fi

  # swap: repo folder -> generated proof
  rm -rf "$target"
  cp -r "$src" "$target"

  # WARM the dependency cache (untimed): this builds the proof AND every cited-prop /
  # shared-library / Mathlib-tactic olean it needs. Those deps are the repo's OWN proofs,
  # identical across arms/attempts, and are NOT part of the produced proof we're timing.
  ( cd "$LAKE" && timeout -k 30 "$CAP" lake build "$tgt" ) >>"$LOGF" 2>&1
  # Invalidate ONLY this proposition's own artifacts, so the timed build recompiles just
  # its step*/Main files while every dependency stays warm. -> every attempt (1/2/3) and
  # both arms start from an identical warm state; the first attempt no longer eats the
  # one-time dep-cone build tax.
  rm -rf "$LAKE/.lake/build/lib/$book/$prop" "$LAKE/.lake/build/ir/$book/$prop"

  t0=$(date +%s.%N)
  ( cd "$LAKE" && timeout -k 30 "$CAP" lake build "$tgt" ) >>"$LOGF" 2>&1; rc=$?
  t1=$(date +%s.%N)
  dt=$(awk "BEGIN{printf \"%.2f\", $t1-$t0}")
  if   [ $rc -eq 0   ]; then st=ok
  elif [ $rc -eq 124 ]; then st="T.O."; dt="$CAP"
  else st=fail; fi
  [ $rc -ne 0 ] && { pkill -9 -x z3 2>/dev/null; pkill -9 -x cvc5 2>/dev/null; pkill -9 -x lean 2>/dev/null; sleep 1; }

  # REVERT: drop the swapped-in folder, restore the repo's tracked proof exactly
  rm -rf "$target"
  git -C "$REPO" checkout HEAD -- "LeanEuclidPlus/$book/$prop"

  printf '%s,%s,%s,%s\n' "$label" "$run_id" "$dt" "$st" | tee -a "$out"
  return 0
}

setup() {  # wipe all our built content, rebuild the shared base SystemE (Mathlib reused)
  rm -rf "$LAKE/.lake/build"
  ( cd "$LAKE" && lake build SystemE ) || { echo "FATAL: SystemE build failed"; exit 1; }
}

for run in $(seq 1 "$NUM_RUNS"); do
  STAMP="$(date +%Y%m%d_%H%M%S)"
  PASSDIR="$RESULTS/pass${run}_${STAMP}"; mkdir -p "$PASSDIR"
  LOGF="$PASSDIR/build.log"
  { echo "pass: $run/$NUM_RUNS"; echo "host: $(hostname)"; echo "date: $(date)";
    echo "cap:  ${CAP}s"; echo "git:  $(git -C "$REPO" rev-parse HEAD 2>/dev/null)"; } > "$PASSDIR/meta.txt"
  echo "### PASS $run/$NUM_RUNS -> $PASSDIR"

  for arm in "${ARMS[@]}"; do
    CSV="$PASSDIR/${arm}.csv"; echo "label,run_id,wall_s,status" > "$CSV"
    setup
    for label in "${PROPS[@]}"; do
      armdir="$OUT/$arm/${label}_opus"
      [ -d "$armdir" ] || { echo "  (missing arm dir $armdir — skipping)" >> "$LOGF"; continue; }
      # every run of this (arm,label): SUCCESS -> compile; else nan row (complete data)
      for rundir in "$armdir"/*/; do
        [ -f "$rundir/result.txt" ] || continue
        run_id="$(basename "$rundir")"
        res="$(run_result "$rundir")"
        if [ "$res" = "SUCCESS" ]; then
          measure "$CSV" "$arm" "$label" "$run_id"
        else
          printf '%s,%s,%s,%s\n' "$label" "$run_id" "nan" "${res:-UNKNOWN}" | tee -a "$CSV"
        fi
      done
    done
  done
done
echo "### done: $NUM_RUNS pass(es) under $RESULTS"

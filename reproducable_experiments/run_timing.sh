#!/usr/bin/env bash
# Per-prop compile-time benchmark: faithful Book1 vs original OldBook1.
# Each world runs from a clean build: rm -rf .lake/build -> lake build SystemE -> time targets.
# Mathlib + external deps live in .lake/packages (never wiped). SMT is uncapped (lakefile), so the
# per-prop wall cap ($CAP, default 600s) is the only cutoff. Serial (-j1), one target at a time.
set -uo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
LAKE="$(cd "$HERE/../LeanEuclidPlus" && pwd)"
OUT="$HERE/results"; CAP="${CAP:-600}"; JOBS="${JOBS:-1}"
STAMP="$(date +%Y%m%d_%H%M%S)"; HOST="$(hostname -s)"
mkdir -p "$OUT"; cd "$LAKE"

measure() {  # $1 csv-name  $2 lake-target  $3 outfile
  local name="$1" tgt="$2" out="$3" t0 t1 rc dt st
  t0=$(date +%s.%N); timeout -k 30 "$CAP" lake build -j "$JOBS" "$tgt" >/dev/null 2>&1; rc=$?; t1=$(date +%s.%N)
  dt=$(awk "BEGIN{printf \"%.2f\", $t1-$t0}")
  if   [ $rc -eq 0   ]; then st=ok
  elif [ $rc -eq 124 ]; then st="T.O."; dt="$CAP"
  else st=fail; fi
  printf '%s,%s,%s\n' "$name" "$dt" "$st" | tee -a "$out"
  [ $rc -ne 0 ] && { pkill -9 -x z3 2>/dev/null; pkill -9 -x cvc5 2>/dev/null; pkill -9 -x lean 2>/dev/null; sleep 1; }
  return 0
}

setup() {  # 1) wipe all our built content   2) build shared base SystemE (Mathlib reused from .lake/packages)
  rm -rf "$LAKE/.lake/build"
  lake build SystemE || { echo "FATAL: SystemE build failed"; exit 1; }
}

# ---- NEW: faithful Book1 ----
NEW="$OUT/new_${HOST}_${STAMP}.csv"; echo "### NEW -> $NEW"
setup; echo "target,wall_s,status" > "$NEW"
measure Helpers Helpers "$NEW"
for n in $(seq -w 1 48); do measure "$n" "Book1.Prop$n.Main" "$NEW"; done

# ---- OLD: original OldBook1 ----
OLD="$OUT/old_${HOST}_${STAMP}.csv"; echo "### OLD -> $OLD"
setup; echo "target,wall_s,status" > "$OLD"
for n in $(seq -w 1 48); do measure "$n" "OldBook1.Prop$n" "$OLD"; done

echo "### done: $NEW | $OLD"

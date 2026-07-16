#!/usr/bin/env bash
# Grade one prop, relaxed (same as run_baseline.sh's grade). PASS/FAIL + compile wall time.
# Usage: bash eval.sh <Book> <Prop2digit> [cost_usd] [model]
set -uo pipefail
set +u; source "$HOME/.venvs/leaneuclid/bin/activate" 2>/dev/null; set -u
B="$1"; NN="$2"; COST="${3:-}"; MODEL="${4:-}"
LEP="$(cd "$(dirname "$0")/LeanEuclidPlus" && pwd -P)"; cd "$LEP"
rel="Book${B}/Prop${NN}"

fail=
[ "$(grep -c sorry "$rel/Main.lean")" -eq 0 ]                                  || fail=sorry
[ -n "$fail" ] || python3 scripts/check_faithful.py  --relaxed "$rel/Main.lean" >/dev/null 2>&1 || fail=faithful
[ -n "$fail" ] || python3 scripts/check_signatures.py         "$rel/Main.lean" >/dev/null 2>&1 || fail=signatures
[ -n "$fail" ] || python3 scripts/check_steps.py     --relaxed "$rel/Main.lean" >/dev/null 2>&1 || fail=steps
t0=$(date +%s)
[ -n "$fail" ] || lake build "Book${B}.Prop${NN}.Main" >/dev/null 2>&1           || fail=build
compile_sec=$(( $(date +%s) - t0 ))

[ -z "$fail" ] && verdict=PASS || verdict="FAIL:$fail"
printf 'prop=%s verdict=%s compile_sec=%s%s%s\n' \
  "$rel" "$verdict" "$compile_sec" "${COST:+ cost_usd=$COST}" "${MODEL:+ model=$MODEL}"

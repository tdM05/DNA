#!/usr/bin/env bash
# Revert Euclid props to MAP stage (baseline starting state). Per prop:
#   1. unwire Main (bodies -> ':= by sorry', strips the step-file imports)   [only if wired]
#   2. delete backing stepN.lean files
#   3. strip any `set_option systemE.solverTime ... in` dev cap (no cap in baseline)
# Robust: skips already-map props, continues past failures, and FLAGS anything left non-map
# (e.g. an inline-proved Main with no step files — that one needs a manual git revert).
# Recoverable: everything it touches is tracked; `git checkout -- <path>` restores.
#
# Usage:
#   bash revert_to_map.sh Book1                  # every prop in Book1
#   bash revert_to_map.sh Book1 Book2 Book3      # all three books
#   bash revert_to_map.sh Book1/Prop05           # a single prop (good for a first test)
set -uo pipefail

LEP="$(cd "$(dirname "$0")/../../LeanEuclidPlus" && pwd -P)"
cd "$LEP"

# expand args -> list of prop dirs
targets=()
for a in "$@"; do
  a="${a%/}"
  if [ -f "$a/Main.lean" ]; then
    targets+=("$a")
  elif [ -d "$a" ]; then
    for d in "$a"/Prop*; do [ -f "$d/Main.lean" ] && targets+=("$d"); done
  else
    echo "skip (not a book or prop): $a"
  fi
done
[ ${#targets[@]} -eq 0 ] && { echo "usage: bash revert_to_map.sh Book1 [Book2 ...] | Book1/Prop05"; exit 1; }

reverted=0; failed=0; flagged=0
for p in "${targets[@]}"; do
  main="$p/Main.lean"
  # 1. try unwire if step files exist; tolerate failure (Main may already be at map, with
  #    only ORPHAN step files left over — that's fine, we clean them below).
  if ls "$p"/step*.lean >/dev/null 2>&1; then
    python3 scripts/wire_main.py "$p" --unwire >/dev/null 2>&1 || true
  fi
  # 2. only if Main STILL imports a step file is it genuinely wired (unwire truly failed) —
  #    deleting the steps then would break the build, so skip + flag.
  if grep -q 'import .*\.step[0-9]' "$main"; then
    echo "STILL WIRED (unwire failed): $p — skipped to avoid breakage"; failed=$((failed+1)); continue
  fi
  # 3. safe now: delete backing/orphan step files + strip any solverTime dev cap
  rm -f "$p"/step*.lean
  sed -i '/set_option systemE\.solverTime/d' "$main"
  # report + flag if it did NOT end at map stage (no sorry bodies => inline-proved, manual revert needed)
  sc=$(grep -c ':= by sorry' "$main")
  if [ "$sc" -eq 0 ]; then
    echo "!! $p  — 0 sorry bodies (inline-proved? needs manual: git checkout <map-commit> -- $main)"
    flagged=$((flagged+1))
  else
    echo "   $p  -> map ($sc sorry bodies)"
    reverted=$((reverted+1))
  fi
done

echo
echo "=== $reverted reverted to map · $failed unwire-failed · $flagged flagged (not map) ==="
echo "sanity:  find Book1 Book2 Book3 -name 'step*.lean' 2>/dev/null | wc -l    # want 0"
echo "         grep -rl 'systemE.solverTime' Book1 Book2 Book3 --include=Main.lean  # want none"

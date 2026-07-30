#!/usr/bin/env bash
#
# count_gaps.sh — reproducible tally of Euclid gap / assumption markers.
#
# WHY THIS EXISTS: the gap numbers we report (17 @euclid_gap, 33 @assumption_gap)
# must be independently re-derivable by a reviewer. This script is that source of
# truth: a plain grep, scoped to the real proposition trees, with every matched
# line printed so nothing is hidden behind a raw count.
#
# WHAT IT COUNTS (only inside the *authoritative* proof trees):
#   LeanEuclidF/Book1/  Book2/  Book3/
#
# WHAT IT EXCLUDES (and why):
#   - OldBook1/, OldBook1Variants/  : frozen benchmark baseline, off-limits (see CLAUDE.md)
#   - LeanEuclidF/accept_refute/ : test fixtures, not real propositions
#   - anything outside Book1/2/3    : Helpers/, SystemE/, etc. carry no gap markers
#
# MARKER SEMANTICS (per CLAUDE.md):
#   @euclid_gap      = a genuine gap in EUCLID's proof (a generic-position fact he reads
#                      off the figure, unstated, FALSE in an admissible degenerate model).
#                      These are the defensible "gaps we found in the paper".
#   @assumption_gap  = a consumed premise the triviality ladder could NOT auto-close, so
#                      Phase B proves it as a normal lemma. By definition NOT a gap in
#                      Euclid — an entailed-but-nontrivial-to-automate fact.
#   @suppress_deps_check = marks a wrong-proposition citation in the SOURCE EDITION (e.g.
#                      Fitzpatrick bracketing segment-bisection as [Prop.~1.9], an angle
#                      prop). This IS a genuine gap/defect we found — but a CITATION-metadata
#                      gap in the outside source, NOT a gap in EUCLID's proof and NOT our
#                      formalization's fault. Track it as its own kind of gap, separate from
#                      the two proof categories above; do not merge it into the @euclid_gap
#                      "gaps in the paper's reasoning" count.
#
# NOTE on @euclid_gap: three prose cross-references (e.g. "Helper for the two euclid_gap
# branches") were deliberately written WITHOUT the leading '@' so this grep matches only
# real gap-MARKING sites. If you re-introduce an '@' in prose, this count will over-report.
#
# USAGE:  bash scripts/count_gaps.sh          # summary + per-line listing
#         bash scripts/count_gaps.sh --quiet  # summary counts only
#
# Run from the repo root (…/Pistis). Read-only; mutates nothing.

set -euo pipefail

QUIET=0
[[ "${1:-}" == "--quiet" ]] && QUIET=1

# The authoritative proof trees. OldBook1* and accept_refute/ are intentionally absent.
BOOK_DIRS=(LeanEuclidF/Book1 LeanEuclidF/Book2 LeanEuclidF/Book3)

# Sanity: refuse to run from the wrong directory rather than silently report 0.
for d in "${BOOK_DIRS[@]}"; do
  if [[ ! -d "$d" ]]; then
    echo "ERROR: '$d' not found. Run this from the repo root (…/Pistis)." >&2
    exit 1
  fi
done

# grep helper: recursive, .lean only, fixed-string marker, over the Book trees.
# Prints "path:line:  <matched line>". Returns matches on stdout (empty if none).
matches () {
  local marker="$1"
  grep -rn --include='*.lean' -F -- "$marker" "${BOOK_DIRS[@]}" 2>/dev/null || true
}

# per-book breakdown of a marker's matches
per_book () {
  local marker="$1"
  matches "$marker" | grep -oE 'LeanEuclidF/Book[0-9]+' | sort | uniq -c
}

report () {
  local marker="$1" label="$2"
  local hits total
  hits="$(matches "$marker")"
  total="$(printf '%s' "$hits" | grep -c . || true)"

  echo "=================================================================="
  echo "  ${marker}   (${label})"
  echo "  TOTAL in Book1/2/3: ${total}"
  echo "  by book:"
  per_book "$marker" | sed 's/^/     /'
  if [[ "$QUIET" -eq 0 && "$total" -gt 0 ]]; then
    echo "  ----- matched lines -----"
    printf '%s\n' "$hits" | sed 's/^/     /'
  fi
  echo
}

echo
echo "Gap-marker tally over ${BOOK_DIRS[*]}"
echo "(excludes OldBook1*, accept_refute/, and everything outside Book1/2/3)"
echo

report "@euclid_gap"         "genuine gaps in Euclid's proof"
report "@assumption_gap"     "entailed premises Phase B proves — NOT Euclid gaps"
report "@suppress_deps_check" "source-edition citation gaps — a distinct gap type, NOT proof gaps"

echo "=================================================================="
echo "Cross-check: any markers OUTSIDE Book1/2/3 (should be fixtures/none):"
for m in "@euclid_gap" "@assumption_gap" "@suppress_deps_check"; do
  n="$(grep -rn --include='*.lean' -F -- "$m" LeanEuclidF/ 2>/dev/null \
        | grep -vE 'LeanEuclidF/Book[123]/' | grep -c . || true)"
  echo "   ${m}: ${n} outside Book1/2/3"
done
echo "=================================================================="

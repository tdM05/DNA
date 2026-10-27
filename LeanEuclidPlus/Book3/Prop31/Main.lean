import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem proposition_31 : ∀ (a b c d e : Point) (ABCD : Circle) (AC BD : Line),
  a.onCircle ABCD ∧ b.onCircle ABCD ∧ c.onCircle ABCD ∧ d.onCircle ABCD ∧
  e.isCentre ABCD ∧
  between b e c ∧
  distinctPointsOnLine a c AC ∧
  distinctPointsOnLine b d BD ∧
  b.opposingSides d AC ∧
  a.opposingSides c BD →
  ∠ b:a:c = ∟ ∧ ∠ a:b:c < ∟ ∧ ∠ a:d:c > ∟ := by
  sorry

end Elements.Book3

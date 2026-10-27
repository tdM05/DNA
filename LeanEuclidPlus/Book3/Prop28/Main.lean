import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3


theorem proposition_28 : ∀ (a b d e k l : Point) (ABC DEF : Circle),
  a.onCircle ABC ∧ b.onCircle ABC ∧
  d.onCircle DEF ∧ e.onCircle DEF ∧
  k.isCentre ABC ∧ l.isCentre DEF ∧
  |(k─a)| = |(l─d)| ∧
  a ≠ b ∧ d ≠ e ∧
  |(a─b)| = |(d─e)| →
  ∠ a:k:b = ∠ d:l:e := by
  sorry

end Elements.Book3

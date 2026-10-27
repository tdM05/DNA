import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step17_perp
  (a e f : Point) (DA : Line)
  (haDA : a.onLine DA)
  (hperp : ∀ p : Point, p.onLine DA → p ≠ f → ∠ p:f:e = ∟)
  (step17_af : a ≠ f)
  : ∠ a:f:e = ∟ := by
  exact hperp a haDA step17_af

end Elements.Book3

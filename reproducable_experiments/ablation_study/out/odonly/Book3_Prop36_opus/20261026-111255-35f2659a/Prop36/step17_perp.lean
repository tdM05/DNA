import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step17_perp (a c e f : Point) (DA : Line)
  (haDA : a.onLine DA)
  (hperpall : ∀ p : Point, p.onLine DA → p ≠ f → ∠ p:f:e = ∟)
  (hbet : between a f c) :
    ∠ a:f:e = ∟ := by
  have haf : a ≠ f := by euclid_finish
  exact hperpall a haDA haf

end Elements.Book3

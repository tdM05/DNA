import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_26_step25 (a b c e f h : Point) (AH : Line)
    (h_bhc : between b h c) (h_bh : |(b─h)| = |(e─f)|)
    (h_a_AH : a.onLine AH) (h_h_AH : h.onLine AH) :
    between b h c ∧ |(b─h)| = |(e─f)| ∧ a.onLine AH ∧ h.onLine AH := by
  euclid_finish

end Elements.Book1

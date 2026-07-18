import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_26_step24 (b c e f : Point)
    (hne2 : |(b─c)| ≠ |(e─f)|) :
    |(b─c)| > |(e─f)| ∨ |(e─f)| > |(b─c)| := by
  rcases lt_or_gt_of_ne hne2 with h | h
  · right; exact h
  · left; exact h

end Elements.Book1

import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_26_step1 (a b d e : Point)
    (hne : |(a─b)| ≠ |(d─e)|) :
    |(a─b)| > |(d─e)| ∨ |(d─e)| > |(a─b)| := by
  rcases lt_or_gt_of_ne hne with h | h
  · right; exact h
  · left; exact h

end Elements.Book1

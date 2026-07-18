import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_26_step13 (a b d e : Point)
    (step12 : ¬(|(a─b)| ≠ |(d─e)|)) :
    |(a─b)| = |(d─e)| := by
  by_contra h
  exact step12 h

end Elements.Book1

import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
theorem helper_2_4_step1 (a b d e : Point) (AB DE AD BE : Line)
    (h1 : |(a─d)| = |(a─b)|) (h2 : |(b─e)| = |(a─b)|) (h3 : |(d─e)| = |(a─b)|)
    (h4 : ∠ b:a:d = ∟) (h5 : ∠ a:d:e = ∟) (h6 : ∠ a:b:e = ∟) (h7 : ∠ b:e:d = ∟) :
    |(a─d)| = |(a─b)| ∧ |(b─e)| = |(a─b)| ∧ |(d─e)| = |(a─b)| ∧
      (∠ b:a:d = ∟) ∧ (∠ a:d:e = ∟) ∧ (∠ a:b:e = ∟) ∧ (∠ b:e:d = ∟) :=
  ⟨h1, h2, h3, h4, h5, h6, h7⟩

end Elements.Book2

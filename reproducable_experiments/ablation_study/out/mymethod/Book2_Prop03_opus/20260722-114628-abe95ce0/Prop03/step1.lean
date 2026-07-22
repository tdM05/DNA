import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_3_step1 (b c d e : Point)
    (h1 : |(c─d)| = |(c─b)|) (h2 : |(b─e)| = |(c─b)|) (h3 : |(d─e)| = |(c─b)|)
    (h4 : ∠ b:c:d = ∟) (h5 : ∠ c:d:e = ∟) (h6 : ∠ c:b:e = ∟) (h7 : ∠ b:e:d = ∟) :
    |(c─d)| = |(c─b)| ∧ |(b─e)| = |(c─b)| ∧ |(d─e)| = |(c─b)| ∧
      (∠ b:c:d = ∟) ∧ (∠ c:d:e = ∟) ∧ (∠ c:b:e = ∟) ∧ (∠ b:e:d = ∟) :=
  ⟨h1, h2, h3, h4, h5, h6, h7⟩

end Elements.Book2

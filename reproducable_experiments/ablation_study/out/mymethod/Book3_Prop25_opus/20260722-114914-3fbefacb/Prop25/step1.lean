import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_step1 (a d c : Point)
    (h1 : between a d c) (h2 : |(a─d)| = |(d─c)|) :
    between a d c ∧ |(a─d)| = |(d─c)| := ⟨h1, h2⟩

end Elements.Book3

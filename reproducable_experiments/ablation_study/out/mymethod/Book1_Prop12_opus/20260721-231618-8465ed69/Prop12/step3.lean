import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_12_step3 (e g h : Point)
    (h1 : between e h g) (h2 : |(e─h)| = |(h─g)|) :
    between e h g ∧ |(e─h)| = |(h─g)| := by
  exact ⟨h1, h2⟩

end Elements.Book1

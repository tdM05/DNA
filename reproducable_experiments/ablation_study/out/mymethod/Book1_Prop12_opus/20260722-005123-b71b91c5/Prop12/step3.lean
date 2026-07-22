import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_12_step3 (e h g : Point)
    (hbet : between e h g) (hlen : |(e─h)| = |(h─g)|) :
    between e h g ∧ |(e─h)| = |(h─g)| := by
  exact ⟨hbet, hlen⟩

end Elements.Book1

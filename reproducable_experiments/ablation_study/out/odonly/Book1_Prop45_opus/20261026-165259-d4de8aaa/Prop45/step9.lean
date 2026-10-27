import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step9 (g h k m : Point) (GH : Line)
  (hmGH : ¬m.onLine GH) (hkGH : ¬k.onLine GH) (hmk : ¬m.sameSide k GH)
  (hstep8 : ∠ k:h:g + ∠ g:h:m = ∟ + ∟)
  : k.opposingSides m GH ∧ (∠ k:h:g + ∠ g:h:m = ∟ + ∟) := by euclid_finish

end Elements.Book1

import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step9
  (g h k m : Point) (GH : Line)
  (hk_off : ¬k.onLine GH) (hm_off : ¬m.onLine GH)
  (hmk_ss : ¬m.sameSide k GH)
  (step8 : ∠ k:h:g + ∠ g:h:m = ∟ + ∟) :
  k.opposingSides m GH ∧ (∠ k:h:g + ∠ g:h:m = ∟ + ∟) := by
  euclid_finish

end Elements.Book1

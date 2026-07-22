import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step9 (g h k m : Point) (GH : Line)
    (hkGH : ¬ k.onLine GH) (hmGH : ¬ m.onLine GH) (hmk : ¬ m.sameSide k GH)
    (hstep8 : ∠ k:h:g + ∠ g:h:m = ∟ + ∟) :
    k.opposingSides m GH ∧ (∠ k:h:g + ∠ g:h:m = ∟ + ∟) := by
  euclid_finish

end Elements.Book1

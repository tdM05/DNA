import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_47_step2
    (a : Point) (AL BD CE : Line)
    (haAL : a.onLine AL) (hALBD : ¬AL.intersectsLine BD) :
    a.onLine AL ∧ (¬(AL.intersectsLine BD) ∨ ¬(AL.intersectsLine CE)) :=
  ⟨haAL, Or.inl hALBD⟩

end Elements.Book1

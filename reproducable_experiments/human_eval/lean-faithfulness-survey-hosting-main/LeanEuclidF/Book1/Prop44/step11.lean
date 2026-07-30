import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1
open Elements

theorem h_1_44_s11
    (k : Point) (KL AB : Line)
    (hkKL : k.onLine KL)
    (hKLAB : ¬KL.intersectsLine AB)
    : k.onLine KL ∧ ¬(KL.intersectsLine AB) :=
  ⟨hkKL, hKLAB⟩

end Elements.Book1

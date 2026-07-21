import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_30_step1 (AB CD EF GK : Line) (g h k : Point)
    (hgAB : g.onLine AB) (hgGK : g.onLine GK)
    (hhEF : h.onLine EF) (hhGK : h.onLine GK)
    (hkCD : k.onLine CD) (hkGK : k.onLine GK)
    (hABEF : ¬AB.intersectsLine EF) (hCDEF : ¬CD.intersectsLine EF)
    (hABCD : AB ≠ CD) (hCDEF2 : CD ≠ EF) (hEFAB : EF ≠ AB) :
    AB.intersectsLine GK ∧ EF.intersectsLine GK ∧ CD.intersectsLine GK := by
  euclid_finish

end Elements.Book1

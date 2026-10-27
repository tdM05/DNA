import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_30_step1 (g h k : Point) (AB CD EF GK : Line)
    (hg_ab : g.onLine AB) (hg_gk : g.onLine GK)
    (hh_ef : h.onLine EF) (hh_gk : h.onLine GK)
    (hk_cd : k.onLine CD) (hk_gk : k.onLine GK)
    (hcd_ef : CD ≠ EF) (hef_ab : EF ≠ AB)
    (hAB_EF : ¬AB.intersectsLine EF) (hCD_EF : ¬CD.intersectsLine EF) :
    AB.intersectsLine GK ∧ EF.intersectsLine GK ∧ CD.intersectsLine GK := by
  have h1 : AB.intersectsLine GK := by euclid_finish
  have h2 : EF.intersectsLine GK := by euclid_finish
  have h3 : CD.intersectsLine GK := by euclid_finish
  exact ⟨h1, h2, h3⟩

end Elements.Book1

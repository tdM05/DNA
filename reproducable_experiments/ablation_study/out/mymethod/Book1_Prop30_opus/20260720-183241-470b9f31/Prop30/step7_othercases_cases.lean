import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_30_step7_othercases_cases (GK : Line) (g h k : Point)
  (hg_gk : g.onLine GK) (hh_gk : h.onLine GK) (hk_gk : k.onLine GK)
  (hgh_ne : g ≠ h) (hkh_ne : k ≠ h) (hgk_ne : g ≠ k)
  (hnbtw : ¬between g h k) :
  between h g k ∨ between g k h := by
  euclid_apply (between_points g h k GK)
  euclid_finish

end Elements.Book1

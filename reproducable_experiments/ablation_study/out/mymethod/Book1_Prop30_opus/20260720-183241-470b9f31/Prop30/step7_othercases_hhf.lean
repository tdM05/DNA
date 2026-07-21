import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_30_step7_othercases_hhf (EF GK : Line) (f g h k : Point)
  (hg_gk : g.onLine GK) (hh_gk : h.onLine GK) (hk_gk : k.onLine GK)
  (hh_ef : h.onLine EF) (hf_ef : f.onLine EF)
  (hgh_ne : g ≠ h) (hkh_ne : k ≠ h) (hgk_ne : g ≠ k)
  (hnbtw : ¬between g h k) (hf_off : ¬f.onLine GK) :
  ∠ g:h:f = ∠ k:h:f := by
  -- rays h→g and h→k coincide (h is not between g,k), so the angles to f are equal
  euclid_apply (equal_angles h g k f f GK EF)
  euclid_finish

end Elements.Book1

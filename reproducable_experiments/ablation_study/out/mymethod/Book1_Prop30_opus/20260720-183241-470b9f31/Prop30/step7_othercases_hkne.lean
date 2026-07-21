import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_30_step7_othercases_hkne (CD EF : Line) (k h : Point)
  (hk_cd : k.onLine CD) (hh_ef : h.onLine EF)
  (hcd_ef : ¬CD.intersectsLine EF) (hne_cd_ef : CD ≠ EF) :
  k ≠ h := by
  intro heq
  euclid_apply (intersection_lines_common_point k CD EF)
  euclid_finish

end Elements.Book1

import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_30_step7_othercases_cdgk (CD EF GK : Line) (h : Point)
  (hh_ef : h.onLine EF) (hh_gk : h.onLine GK)
  (hcd_ef : ¬CD.intersectsLine EF) (hne_cd_ef : CD ≠ EF) :
  CD ≠ GK := by
  intro heq
  euclid_apply (intersection_lines_common_point h CD EF)
  euclid_finish

end Elements.Book1

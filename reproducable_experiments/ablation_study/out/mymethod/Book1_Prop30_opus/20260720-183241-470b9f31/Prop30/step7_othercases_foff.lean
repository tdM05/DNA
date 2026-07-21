import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_30_step7_othercases_foff (EF GK : Line) (e f h : Point)
  (hf_ef : f.onLine EF) (hh_ef : h.onLine EF) (hh_gk : h.onLine GK) (hehf : between e h f)
  (hef_gk : EF ≠ GK) :
  ¬f.onLine GK := by euclid_finish

end Elements.Book1

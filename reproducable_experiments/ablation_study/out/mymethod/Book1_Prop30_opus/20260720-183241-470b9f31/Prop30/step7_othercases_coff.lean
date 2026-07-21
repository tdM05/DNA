import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_30_step7_othercases_coff (CD GK : Line) (c d k : Point)
  (hc_cd : c.onLine CD) (hk_cd : k.onLine CD) (hk_gk : k.onLine GK) (hckd : between c k d)
  (hcd_gk : CD ≠ GK) :
  ¬c.onLine GK := by euclid_finish

end Elements.Book1

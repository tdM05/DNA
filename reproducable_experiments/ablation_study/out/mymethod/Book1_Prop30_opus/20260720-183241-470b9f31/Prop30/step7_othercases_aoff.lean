import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_30_step7_othercases_aoff (AB GK : Line) (a g : Point)
  (ha_ab : a.onLine AB) (hg_ab : g.onLine AB) (hg_gk : g.onLine GK) (hga_ne : g ≠ a)
  (hab_gk : AB ≠ GK) :
  ¬a.onLine GK := by euclid_finish

end Elements.Book1

import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_11_step2 (a f g : Point) (ABC ADE : Circle) (AF AG : Line)
  (ha_ABC : a.onCircle ABC) (hf_c : f.isCentre ABC)
  (ha_ADE : a.onCircle ADE) (hg_c : g.isCentre ADE)
  (ha_AF : a.onLine AF) (hf_AF : f.onLine AF)
  (ha_AG : a.onLine AG) (hg_AG : g.onLine AG) :
  distinctPointsOnLine a f AF ∧ distinctPointsOnLine a g AG := by
  euclid_finish

end Elements.Book3

import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_11_step2 (a f g : Point) (ABC ADE : Circle) (AF AG : Line)
    (ha_on_AF : a.onLine AF) (hf_on_AF : f.onLine AF)
    (ha_on_AG : a.onLine AG) (hg_on_AG : g.onLine AG)
    (ha_ABC : a.onCircle ABC) (hf_centre : f.isCentre ABC)
    (ha_ADE : a.onCircle ADE) (hg_centre : g.isCentre ADE) :
    distinctPointsOnLine a f AF ∧ distinctPointsOnLine a g AG := by
  euclid_finish

end Elements.Book3

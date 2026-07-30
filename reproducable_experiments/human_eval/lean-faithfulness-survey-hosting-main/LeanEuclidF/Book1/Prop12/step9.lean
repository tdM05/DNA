import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_12_s9 (e h g : Point) (AB : Line)
    (hbetween : between e h g) (heAB : e.onLine AB) (hgAB : g.onLine AB) :
    h.onLine AB := by
  euclid_finish

end Elements.Book1

import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_47_step13_tri
    (a b d : Point) (AB BD AD : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hbBD : b.onLine BD) (hdBD : d.onLine BD)
    (haAD : a.onLine AD) (hdAD : d.onLine AD)
    (hoffBD : ¬a.onLine BD) (hdoffAB : ¬d.onLine AB) (hab : a ≠ b) (had : a ≠ d) :
    formTriangle a b d AB BD AD := by
  euclid_finish

end Elements.Book1

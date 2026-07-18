import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_47_step11_T1
    (a b d : Point) (AB BD AD : Line)
    (hbBD : b.onLine BD) (hdBD : d.onLine BD)
    (haAD : a.onLine AD) (hdAD : d.onLine AD)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hoffBD : ¬a.onLine BD) (hdoffAB : ¬d.onLine AB) (hab : a ≠ b) (had : a ≠ d) :
    formTriangle b d a BD AD AB := by
  euclid_finish

end Elements.Book1

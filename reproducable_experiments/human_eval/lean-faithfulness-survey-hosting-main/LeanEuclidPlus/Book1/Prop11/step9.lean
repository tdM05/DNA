import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_11_s9
    (a b c d e : Point) (AB : Line)
    (hacb : between a c b)
    (ha : a.onLine AB) (hb : b.onLine AB)
    (hdAB : d.onLine AB)
    (hadc : between a d c) (hceb : between c e b) :
    between d c e := by
  euclid_finish

end Elements.Book1

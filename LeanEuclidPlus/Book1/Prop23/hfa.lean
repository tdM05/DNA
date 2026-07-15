import SystemE

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_23_hfa (a f : Point) (AB : Line)
    (ha_AB : a.onLine AB) (hfoff : ¬f.onLine AB)
    : f ≠ a := by
  euclid_finish

end Elements.Book1

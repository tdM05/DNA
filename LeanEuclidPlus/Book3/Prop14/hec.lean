import SystemE

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem helper_3_14_hec
    (c e : Point) (ABDC : Circle)
    (hc : c.onCircle ABDC) (hcen : e.isCentre ABDC) :
    e ≠ c := by euclid_finish

end Elements.Book3

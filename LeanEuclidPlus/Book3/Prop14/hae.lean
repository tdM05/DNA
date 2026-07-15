import SystemE

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem helper_3_14_hae
    (a e : Point) (ABDC : Circle)
    (ha : a.onCircle ABDC) (hcen : e.isCentre ABDC) :
    a ≠ e := by euclid_finish

end Elements.Book3

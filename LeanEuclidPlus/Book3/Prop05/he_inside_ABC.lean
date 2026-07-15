import SystemE

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem helper_3_5_he_inside_ABC (ABC : Circle) (e : Point)
    (hecABC : e.isCentre ABC)
    : e.insideCircle ABC := by
  euclid_finish

end Elements.Book3

import SystemE

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem helper_3_5_hne_ec (ABC : Circle) (e c : Point)
    (hecABC : e.isCentre ABC) (hcABC : c.onCircle ABC)
    : e ≠ c := by
  euclid_finish

end Elements.Book3

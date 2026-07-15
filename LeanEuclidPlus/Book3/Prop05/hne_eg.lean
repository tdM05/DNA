import SystemE

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem helper_3_5_hne_eg (CDG : Circle) (e g : Point)
    (hecdg : e.isCentre CDG) (hgCDG : g.onCircle CDG)
    : e ≠ g := by
  euclid_finish

end Elements.Book3

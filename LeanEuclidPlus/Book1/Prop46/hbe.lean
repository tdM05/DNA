import SystemE

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_46_hbe
    (a b d e : Point)
    (step2 : |(a─d)| = |(a─b)|)
    (step7 : |(a─d)| = |(b─e)|) :
    |(b─e)| = |(a─b)| := by
  euclid_finish

end Elements.Book1

import SystemE

namespace Elements.Book3

theorem helper_3_11_step5 (a g d : Point) (ADE : Circle)
    (h1 : g.isCentre ADE) (h2 : a.onCircle ADE) (h3 : d.onCircle ADE) :
    |(a─g)| = |(g─d)| := by
  euclid_finish

end Elements.Book3

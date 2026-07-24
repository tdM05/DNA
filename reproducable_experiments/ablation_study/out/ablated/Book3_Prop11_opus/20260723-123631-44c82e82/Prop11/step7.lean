import SystemE

namespace Elements.Book3

theorem helper_3_11_step7 (g d h : Point) (ADE : Circle)
    (h1 : |(g─d)| > |(g─h)|) (h2 : g.isCentre ADE) (h3 : d.onCircle ADE)
    (h4 : h.outsideCircle ADE) :
    False := by
  euclid_finish

end Elements.Book3

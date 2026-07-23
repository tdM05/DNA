import SystemE

namespace Elements.Book3

theorem helper_3_11_step6 (a g d h : Point)
    (h1 : |(a─g)| > |(g─h)|)
    (h2 : |(a─g)| = |(g─d)|) :
    |(g─d)| > |(g─h)| := by
  euclid_finish

end Elements.Book3

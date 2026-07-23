import SystemE

namespace Elements.Book3

theorem helper_3_11_step4 (a f g h : Point)
    (h1 : |(a─g)| > |(f─h)| - |(g─f)|) (h2 : between f g h) :
    |(a─g)| > |(g─h)| := by
  euclid_finish

end Elements.Book3

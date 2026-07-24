import SystemE

namespace Elements.Book3

theorem helper_3_11_step3 (a f g h : Point)
    (h1 : |(f─a)| = |(f─h)|) (h2 : |(a─g)| + |(g─f)| > |(f─h)|) :
    |(a─g)| > |(f─h)| - |(g─f)| := by
  euclid_finish

end Elements.Book3

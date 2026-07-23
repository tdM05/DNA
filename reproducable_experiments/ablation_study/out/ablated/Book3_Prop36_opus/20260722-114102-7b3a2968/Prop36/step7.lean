import SystemE

namespace Elements.Book3

theorem helper_3_36_step7 (a b c d f : Point)
    (h1 : |(d─a)| * |(d─c)| + |(f─c)| * |(f─c)| = |(f─d)| * |(f─d)|)
    (h2 : |(f─c)| = |(f─b)|) :
    |(d─a)| * |(d─c)| + |(f─b)| * |(f─b)| = |(f─d)| * |(f─d)| := by
  euclid_finish

end Elements.Book3

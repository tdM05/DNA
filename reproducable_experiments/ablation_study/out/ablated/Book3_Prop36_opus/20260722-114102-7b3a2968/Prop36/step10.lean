import SystemE

namespace Elements.Book3

theorem helper_3_36_step10 (a b c d f : Point)
    (h1 : |(d─a)| * |(d─c)| + |(f─b)| * |(f─b)| = |(f─b)| * |(f─b)| + |(d─b)| * |(d─b)|) :
    |(d─a)| * |(d─c)| = |(d─b)| * |(d─b)| := by
  euclid_finish

end Elements.Book3

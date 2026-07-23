import SystemE

namespace Elements.Book3

theorem helper_3_36_step21 (a c d e f : Point)
    (h1 : |(d─a)| * |(d─c)| + |(f─c)| * |(f─c)| = |(f─d)| * |(f─d)|) :
    |(d─a)| * |(d─c)| + |(f─c)| * |(f─c)| + |(e─f)| * |(e─f)| =
      |(f─d)| * |(f─d)| + |(e─f)| * |(e─f)| := by
  euclid_finish

end Elements.Book3

import SystemE

namespace Elements.Book3

theorem helper_3_36_step27 (a c d e b : Point)
    (h1 : |(d─a)| * |(d─c)| + |(e─c)| * |(e─c)| = |(e─d)| * |(e─d)|)
    (h2 : |(e─c)| = |(e─b)|) :
    |(d─a)| * |(d─c)| + |(e─b)| * |(e─b)| = |(e─d)| * |(e─d)| := by
  euclid_finish

end Elements.Book3

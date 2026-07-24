import SystemE

namespace Elements.Book3

-- subtract the (square) on EB from both sides of step29.
theorem helper_3_36_step30 (a b c d e : Point)
    (h1 : |(d─a)| * |(d─c)| + |(e─b)| * |(e─b)| = |(e─b)| * |(e─b)| + |(d─b)| * |(d─b)|) :
    |(d─a)| * |(d─c)| = |(d─b)| * |(d─b)| := by
  euclid_finish

end Elements.Book3

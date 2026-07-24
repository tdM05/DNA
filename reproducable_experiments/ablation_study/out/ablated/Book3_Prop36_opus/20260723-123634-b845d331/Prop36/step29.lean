import SystemE

namespace Elements.Book3

-- combine step27 and step28.
theorem helper_3_36_step29 (a b c d e : Point)
    (h1 : |(d─a)| * |(d─c)| + |(e─b)| * |(e─b)| = |(e─d)| * |(e─d)|)
    (h2 : |(e─b)| * |(e─b)| + |(d─b)| * |(d─b)| = |(e─d)| * |(e─d)|) :
    |(d─a)| * |(d─c)| + |(e─b)| * |(e─b)| = |(e─b)| * |(e─b)| + |(d─b)| * |(d─b)| := by
  euclid_finish

end Elements.Book3

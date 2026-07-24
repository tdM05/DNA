import SystemE

namespace Elements.Book3

-- combine step22 (= AD·DC + CF² + FE² = FD² + FE²), step23 (EC² = CF² + FE²) and
-- step24 (ED² = DF² + FE²): AD·DC + EC² = ED².
theorem helper_3_36_step25 (a c d e f : Point)
    (h1 : |(d─a)| * |(d─c)| + |(f─c)| * |(f─c)| + |(e─f)| * |(e─f)| =
      |(f─d)| * |(f─d)| + |(e─f)| * |(e─f)|)
    (h2 : |(e─c)| * |(e─c)| = |(f─c)| * |(f─c)| + |(e─f)| * |(e─f)|)
    (h3 : |(e─d)| * |(e─d)| = |(d─f)| * |(d─f)| + |(f─e)| * |(f─e)|) :
    |(d─a)| * |(d─c)| + |(e─c)| * |(e─c)| = |(e─d)| * |(e─d)| := by
  euclid_finish

end Elements.Book3

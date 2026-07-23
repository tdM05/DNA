import SystemE

namespace Elements.Book3

-- Combine step 22 (rectangle + squares on $CF$,$FE$ = squares on $FD$,$FE$) with the two
-- Pythagoras identities (steps 23, 24): $|EC|^2 = |CF|^2 + |FE|^2$ and $|ED|^2 = |DF|^2 + |FE|^2$.
theorem helper_3_36_step25 (a c d e f : Point)
    (h1 : |(d─a)| * |(d─c)| + |(f─c)| * |(f─c)| + |(e─f)| * |(e─f)| =
      |(f─d)| * |(f─d)| + |(e─f)| * |(e─f)|)
    (h2 : |(e─c)| * |(e─c)| = |(f─c)| * |(f─c)| + |(e─f)| * |(e─f)|)
    (h3 : |(e─d)| * |(e─d)| = |(d─f)| * |(d─f)| + |(f─e)| * |(f─e)|) :
    |(d─a)| * |(d─c)| + |(e─c)| * |(e─c)| = |(e─d)| * |(e─d)| := by
  euclid_finish

end Elements.Book3

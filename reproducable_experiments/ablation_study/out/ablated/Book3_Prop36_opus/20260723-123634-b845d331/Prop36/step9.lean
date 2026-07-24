import SystemE

namespace Elements.Book3

-- combine step7 and step8.
theorem helper_3_36_step9 (a b c d f : Point)
    (h1 : |(d─a)| * |(d─c)| + |(f─b)| * |(f─b)| = |(f─d)| * |(f─d)|)
    (h2 : |(f─d)| * |(f─d)| = |(f─b)| * |(f─b)| + |(d─b)| * |(d─b)|) :
    |(d─a)| * |(d─c)| + |(f─b)| * |(f─b)| = |(f─b)| * |(f─b)| + |(d─b)| * |(d─b)| := by
  euclid_finish

end Elements.Book3

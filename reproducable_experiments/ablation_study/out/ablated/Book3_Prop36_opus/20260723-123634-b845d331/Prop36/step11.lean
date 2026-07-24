import SystemE

namespace Elements.Book3

-- the remaining (rectangle contained) by AD and DC is equal to the (square) on the tangent DB.
theorem helper_3_36_step11 (a b c d : Point)
    (h1 : |(d─a)| * |(d─c)| = |(d─b)| * |(d─b)|) :
    |(d─a)| * |(d─c)| = |(d─b)| * |(d─b)| := by
  euclid_finish

end Elements.Book3

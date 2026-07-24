import SystemE

namespace Elements.Book2

-- Let the (square) on $DB$ be added to both (sides of step1).
theorem helper_2_12_step2 (a b c d : Point)
    (h1 : |(d─c)| * |(d─c)| = |(c─a)| * |(c─a)| + |(a─d)| * |(a─d)| + 2 * (|(c─a)| * |(a─d)|)) :
    |(d─c)| * |(d─c)| + |(d─b)| * |(d─b)| =
      |(c─a)| * |(c─a)| + |(a─d)| * |(a─d)| + |(d─b)| * |(d─b)| + 2 * (|(c─a)| * |(a─d)|) := by
  linarith

end Elements.Book2

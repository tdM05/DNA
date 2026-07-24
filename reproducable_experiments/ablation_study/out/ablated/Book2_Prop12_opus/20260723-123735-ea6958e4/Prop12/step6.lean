import SystemE

namespace Elements.Book2

-- The square on $CB$ is equal to the (sum of) squares on $CA$ and $AB$, and
-- twice the rectangle contained by $CA$ and $AD$ (combining step3, step4, step5).
theorem helper_2_12_step6 (a b c d : Point)
    (h3 : |(c─d)| * |(c─d)| + |(d─b)| * |(d─b)| =
      |(c─a)| * |(c─a)| + |(a─d)| * |(a─d)| + |(d─b)| * |(d─b)| + 2 * (|(c─a)| * |(a─d)|))
    (h4 : |(c─b)| * |(c─b)| = |(c─d)| * |(c─d)| + |(d─b)| * |(d─b)|)
    (h5 : |(a─b)| * |(a─b)| = |(a─d)| * |(a─d)| + |(d─b)| * |(d─b)|) :
    |(c─b)| * |(c─b)| = |(c─a)| * |(c─a)| + |(a─b)| * |(a─b)| + 2 * (|(c─a)| * |(a─d)|) := by
  linarith

end Elements.Book2

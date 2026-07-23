import SystemE

namespace Elements.Book2

-- Thus, the square on $CB$ is equal to the (sum of the) squares on $CA$ and $AB$, and twice the
-- rectangle contained by $CA$ and $AD$. (Combines steps 3, 4 and 5.)
theorem helper_2_12_step6 (a b c d : Point)
    (h1 : |(c─d)| * |(c─d)| + |(d─b)| * |(d─b)| =
      |(c─a)| * |(c─a)| + |(a─d)| * |(a─d)| + |(d─b)| * |(d─b)| + 2 * (|(c─a)| * |(a─d)|))
    (h2 : |(c─b)| * |(c─b)| = |(c─d)| * |(c─d)| + |(d─b)| * |(d─b)|)
    (h3 : |(a─b)| * |(a─b)| = |(a─d)| * |(a─d)| + |(d─b)| * |(d─b)|) :
    |(c─b)| * |(c─b)| = |(c─a)| * |(c─a)| + |(a─b)| * |(a─b)| + 2 * (|(c─a)| * |(a─d)|) := by
  euclid_finish

end Elements.Book2

import SystemE

namespace Elements.Book2

-- Thus, the (sum of the squares) on $CD$ and $DB$ is equal to the (sum of the) squares on
-- $CA$, $AD$, and $DB$, and twice the [rectangle contained] by $CA$ and $AD$. (Rewrites the
-- left-hand side of step 2 using $DC = CD$.)
theorem helper_2_12_step3 (a b c d : Point)
    (h1 : |(d─c)| * |(d─c)| + |(d─b)| * |(d─b)| =
      |(c─a)| * |(c─a)| + |(a─d)| * |(a─d)| + |(d─b)| * |(d─b)| + 2 * (|(c─a)| * |(a─d)|)) :
    |(c─d)| * |(c─d)| + |(d─b)| * |(d─b)| =
      |(c─a)| * |(c─a)| + |(a─d)| * |(a─d)| + |(d─b)| * |(d─b)| + 2 * (|(c─a)| * |(a─d)|) := by
  euclid_finish

end Elements.Book2

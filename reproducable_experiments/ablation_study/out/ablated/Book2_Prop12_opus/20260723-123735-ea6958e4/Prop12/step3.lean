import SystemE

namespace Elements.Book2

-- The (sum of squares) on $CD$ and $DB$ equals the (sum of) squares on $CA$,
-- $AD$, and $DB$, and twice the [rectangle contained] by $CA$ and $AD$
-- (rewriting $DC$ as $CD$ in step2).
theorem helper_2_12_step3 (a b c d : Point)
    (h1 : |(d─c)| * |(d─c)| + |(d─b)| * |(d─b)| =
      |(c─a)| * |(c─a)| + |(a─d)| * |(a─d)| + |(d─b)| * |(d─b)| + 2 * (|(c─a)| * |(a─d)|)) :
    |(c─d)| * |(c─d)| + |(d─b)| * |(d─b)| =
      |(c─a)| * |(c─a)| + |(a─d)| * |(a─d)| + |(d─b)| * |(d─b)| + 2 * (|(c─a)| * |(a─d)|) := by
  rw [segment_symmetric c d]
  linarith

end Elements.Book2

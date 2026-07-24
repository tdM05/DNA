import SystemE

namespace Elements.Book2

-- The square on $CB$ is greater than the (sum of) squares on $CA$ and $AB$ by
-- twice the rectangle contained by $CA$ and $AD$ (restatement of step6 with
-- segment endpoints reversed).
theorem helper_2_12_step7 (a b c d : Point)
    (h6 : |(c─b)| * |(c─b)| = |(c─a)| * |(c─a)| + |(a─b)| * |(a─b)| + 2 * (|(c─a)| * |(a─d)|)) :
    |(b─c)| * |(b─c)| = |(b─a)| * |(b─a)| + |(a─c)| * |(a─c)| + 2 * (|(c─a)| * |(a─d)|) := by
  rw [segment_symmetric b c, segment_symmetric b a, segment_symmetric a c]
  linarith

end Elements.Book2

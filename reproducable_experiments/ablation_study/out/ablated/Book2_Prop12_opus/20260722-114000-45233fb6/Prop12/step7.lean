import SystemE
import Mathlib.Tactic.LinearCombination

namespace Elements.Book2

theorem helper_2_12_step7 (a b c d : Point)
    (h1 : |(c─b)| * |(c─b)| = |(c─a)| * |(c─a)| + |(a─b)| * |(a─b)| + 2 * (|(c─a)| * |(a─d)|)) :
    |(b─c)| * |(b─c)| = |(b─a)| * |(b─a)| + |(a─c)| * |(a─c)| + 2 * (|(c─a)| * |(a─d)|) := by
  rw [segment_symmetric b c, segment_symmetric b a, segment_symmetric a c]
  linear_combination h1

end Elements.Book2

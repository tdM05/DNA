import SystemE
import Mathlib.Tactic.LinearCombination

namespace Elements.Book2

theorem helper_2_12_step2 (a b c d : Point)
    (h1 : |(d─c)| * |(d─c)| = |(c─a)| * |(c─a)| + |(a─d)| * |(a─d)| + 2 * (|(c─a)| * |(a─d)|)) :
    |(d─c)| * |(d─c)| + |(d─b)| * |(d─b)| =
      |(c─a)| * |(c─a)| + |(a─d)| * |(a─d)| + |(d─b)| * |(d─b)| + 2 * (|(c─a)| * |(a─d)|) := by
  linear_combination h1

end Elements.Book2

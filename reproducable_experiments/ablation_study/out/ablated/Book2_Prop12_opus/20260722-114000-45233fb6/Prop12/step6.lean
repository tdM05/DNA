import SystemE
import Mathlib.Tactic.LinearCombination

namespace Elements.Book2

theorem helper_2_12_step6 (a b c d : Point)
    (h1 : |(c─d)| * |(c─d)| + |(d─b)| * |(d─b)| =
      |(c─a)| * |(c─a)| + |(a─d)| * |(a─d)| + |(d─b)| * |(d─b)| + 2 * (|(c─a)| * |(a─d)|))
    (h2 : |(c─b)| * |(c─b)| = |(c─d)| * |(c─d)| + |(d─b)| * |(d─b)|)
    (h3 : |(a─b)| * |(a─b)| = |(a─d)| * |(a─d)| + |(d─b)| * |(d─b)|) :
    |(c─b)| * |(c─b)| = |(c─a)| * |(c─a)| + |(a─b)| * |(a─b)| + 2 * (|(c─a)| * |(a─d)|) := by
  linear_combination h1 + h2 - h3

end Elements.Book2

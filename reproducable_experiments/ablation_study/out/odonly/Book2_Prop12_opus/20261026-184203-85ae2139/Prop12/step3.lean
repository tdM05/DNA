import SystemE
import Mathlib.Tactic.LinearCombination
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_12_step3
  (a b c d : Point)
  (step2 : |(d─c)| * |(d─c)| + |(d─b)| * |(d─b)| = |(c─a)| * |(c─a)| + |(a─d)| * |(a─d)| + |(d─b)| * |(d─b)| + 2 * (|(c─a)| * |(a─d)|))
  : |(c─d)| * |(c─d)| + |(d─b)| * |(d─b)| = |(c─a)| * |(c─a)| + |(a─d)| * |(a─d)| + |(d─b)| * |(d─b)| + 2 * (|(c─a)| * |(a─d)|) := by
  have hcd : |(c─d)| = |(d─c)| := segment_symmetric c d
  rw [hcd]
  linear_combination step2

end Elements.Book2

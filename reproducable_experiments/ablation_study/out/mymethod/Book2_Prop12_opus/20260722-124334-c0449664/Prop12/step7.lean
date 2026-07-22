import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_12_step7 (a b c d : Point)
    (hstep6 : |(c─b)| * |(c─b)| = |(c─a)| * |(c─a)| + |(a─b)| * |(a─b)| + 2 * (|(c─a)| * |(a─d)|)) :
    |(b─c)| * |(b─c)| = |(b─a)| * |(b─a)| + |(a─c)| * |(a─c)| + 2 * (|(c─a)| * |(a─d)|) := by
  have e1 : |(b─c)| = |(c─b)| := segment_symmetric b c
  have e2 : |(b─a)| = |(a─b)| := segment_symmetric b a
  have e3 : |(a─c)| = |(c─a)| := segment_symmetric a c
  rw [e1, e2, e3]
  linarith

end Elements.Book2

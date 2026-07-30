import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_20_s8 (a b c d : Point)
    (h_btwn : between b a d)
    (h_s6 : |(d─b)| > |(b─c)|)
    (h_s7 : |(d─a)| = |(a─c)|) :
    |(b─a)| + |(a─c)| > |(b─c)| := by
  have h_bd : |(b─a)| + |(a─d)| = |(b─d)| := between_if b a d h_btwn
  linarith [h_bd, h_s6, h_s7, segment_symmetric b d, segment_symmetric d a, segment_symmetric a d]

end Elements.Book1

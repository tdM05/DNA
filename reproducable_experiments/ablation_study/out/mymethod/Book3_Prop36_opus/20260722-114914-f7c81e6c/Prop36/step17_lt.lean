import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step17_lt
  (a e f : Point)
  (hpa : |(a─e)| * |(a─e)| = |(a─f)| * |(a─f)| + |(f─e)| * |(f─e)|)
  (hfa : f ≠ a)
  : |(e─f)| < |(e─a)| := by
  euclid_finish

end Elements.Book3

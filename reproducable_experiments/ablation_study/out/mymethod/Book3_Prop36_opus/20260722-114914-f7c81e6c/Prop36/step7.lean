import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step7
  (a c d f b : Point)
  (step5 : |(d─a)| * |(d─c)| + |(f─c)| * |(f─c)| = |(f─d)| * |(f─d)|)
  (step6 : |(f─c)| = |(f─b)|)
  : |(d─a)| * |(d─c)| + |(f─b)| * |(f─b)| = |(f─d)| * |(f─d)| := by
  rw [← step6]; exact step5

end Elements.Book3

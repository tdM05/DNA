import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_48_s6
    (hstep4 : |(d─a)| * |(d─a)| = |(a─b)| * |(a─b)|)
    : |(d─a)| * |(d─a)| + |(a─c)| * |(a─c)| = |(b─a)| * |(b─a)| + |(a─c)| * |(a─c)| := by
  euclid_finish

end Elements.Book1

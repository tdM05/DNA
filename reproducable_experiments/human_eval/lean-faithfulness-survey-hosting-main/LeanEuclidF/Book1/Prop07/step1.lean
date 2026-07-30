import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_7_s1 (a c d : Point)
    (h : |(a─c)| = |(a─d)|) : |(c─a)| = |(d─a)| := by
  euclid_finish

end Elements.Book1

import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_6_s5 (a b c d : Point) (hbdac : |(b─d)| = |(a─c)|) :
    |(d─b)| = |(a─c)| ∧ |(b─c)| = |(c─b)| := by
  euclid_finish

end Elements.Book1

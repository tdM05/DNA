import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_46_x1
    (a b d e : Point)
    (s2 : |(a─d)| = |(a─b)|)
    (s7 : |(a─d)| = |(b─e)|) :
    |(b─e)| = |(a─b)| := by
  euclid_finish

end Elements.Book1

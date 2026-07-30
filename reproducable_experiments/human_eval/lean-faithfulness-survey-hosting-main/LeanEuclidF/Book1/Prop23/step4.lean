import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_23_s4 (c e a g : Point)
    (h_ag : |(a─g)| = |(c─e)|)
    : |(c─e)| = |(a─g)| := by
  euclid_finish

end Elements.Book1

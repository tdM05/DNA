import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_20_step8 (a b c d : Point)
    (h_step1 : between b a d) (h_step7 : |(d─a)| = |(a─c)|)
    (h_step6 : |(d─b)| > |(b─c)|) :
    |(b─a)| + |(a─c)| > |(b─c)| := by
  euclid_finish

end Elements.Book1

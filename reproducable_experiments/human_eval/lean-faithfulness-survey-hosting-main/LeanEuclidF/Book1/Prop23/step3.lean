import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_23_s3 (c d a f : Point)
    (h_af : |(a─f)| = |(c─d)|)
    : |(c─d)| = |(a─f)| := by
  euclid_finish

end Elements.Book1

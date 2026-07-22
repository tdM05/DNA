import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_step14 (a b c e : Point)
    (h12 : |(a─e)| = |(c─e)|) (h13 : |(a─e)| = |(b─e)|) :
    |(b─e)| = |(c─e)| := by
  euclid_finish

end Elements.Book3

import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_33_hfa
    (a b f : Point)
    (h_afb : between a f b) :
    f ≠ a := by
  euclid_finish

end Elements.Book3

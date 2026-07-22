import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_11_step9 (a f g : Point)
    (step8 : ¬(¬(between f g a))) :
    between f g a := by
  by_contra hc
  exact step8 hc

end Elements.Book3

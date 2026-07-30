import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_36_s6_x1 (a e b : Point) (CH : Line)
  (h_s6_x1 : e.sameSide a CH)
  (h_s6_x2 : a.sameSide b CH) :
  e.sameSide b CH := by
  euclid_apply (same_side_symm e a CH)
  euclid_apply (same_side_trans a e b CH)
  assumption

end Elements.Book1

import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_33_hb_circ_2
    (a b f : Point) (α : Circle)
    (h_afeq : |(a─f)| = |(f─b)|) (h_f_centre : f.isCentre α) (h_a_circ : a.onCircle α) :
    b.onCircle α := by
  euclid_finish

end Elements.Book3

import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_33_step7
    (a b f g : Point)
    (h_afeq : |(a─f)| = |(f─b)|) (h_fg : |(f─g)| = |(f─g)|) :
    |(a─f)| = |(b─f)| ∧ |(f─g)| = |(f─g)| := by
  euclid_finish

end Elements.Book3

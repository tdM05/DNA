import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
theorem helper_2_4_step12 (b c g k : Point)
    (hstep8 : |(b─c)| = |(c─g)|) (hstep9 : |(c─b)| = |(g─k)|)
    (hstep10 : |(c─g)| = |(k─b)|) (hstep11 : |(g─k)| = |(k─b)|)
    : |(c─g)| = |(g─k)| ∧ |(g─k)| = |(k─b)| ∧ |(k─b)| = |(b─c)| := by
  euclid_finish

end Elements.Book2

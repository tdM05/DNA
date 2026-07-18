import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_47_step17_cl_tri
    (a c e : Point) (AC CE AE : Line)
    (haAC : a.onLine AC) (hcAC : c.onLine AC)
    (hcCE : c.onLine CE) (heCE : e.onLine CE)
    (haAE : a.onLine AE) (heAE : e.onLine AE)
    (haoffCE : ¬a.onLine CE) (heoffAC : ¬e.onLine AC) (hac : a ≠ c) (hae : a ≠ e) :
    formTriangle a c e AC CE AE := by
  euclid_finish

end Elements.Book1

import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_47_step17_area_T1
    (a c e : Point) (CE AE AC : Line)
    (hcCE : c.onLine CE) (heCE : e.onLine CE)
    (heAE : e.onLine AE) (haAE : a.onLine AE)
    (haAC : a.onLine AC) (hcAC : c.onLine AC)
    (haoffCE : ¬a.onLine CE) (heoffAC : ¬e.onLine AC) (hac : a ≠ c) (hae : a ≠ e) :
    formTriangle c e a CE AE AC := by
  euclid_finish

end Elements.Book1

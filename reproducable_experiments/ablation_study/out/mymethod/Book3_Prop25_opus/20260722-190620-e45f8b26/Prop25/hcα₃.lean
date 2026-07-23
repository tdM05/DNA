import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_hcα₃ (a c e : Point) (α₃ : Circle)
    (hce : e.isCentre α₃) (hae : a.onCircle α₃)
    (heaec : |(e─a)| = |(e─c)|) :
    c.onCircle α₃ := by
  euclid_apply (point_on_circle_if e a c α₃)
  euclid_finish

end Elements.Book3

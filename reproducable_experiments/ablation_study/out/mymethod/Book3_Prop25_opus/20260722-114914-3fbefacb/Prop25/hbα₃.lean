import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_hbα₃ (a b e : Point) (α₃ : Circle)
    (hec : e.isCentre α₃) (ha : a.onCircle α₃)
    (hEb : |(e─a)| = |(e─b)|) : b.onCircle α₃ := by
  euclid_apply (point_on_circle_if e a b α₃)
  euclid_finish

end Elements.Book3

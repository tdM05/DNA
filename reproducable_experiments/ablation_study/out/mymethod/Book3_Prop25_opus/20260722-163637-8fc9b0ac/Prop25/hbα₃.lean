import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_hbα₃ (a b e : Point) (α₃ : Circle)
    (he_centre : e.isCentre α₃) (ha_circle : a.onCircle α₃)
    (hEb : |(e─a)| = |(e─b)|) :
    b.onCircle α₃ := by
  euclid_finish

end Elements.Book3

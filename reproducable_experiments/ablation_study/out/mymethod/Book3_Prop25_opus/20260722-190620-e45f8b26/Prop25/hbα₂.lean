import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_hbα₂ (a b d : Point) (α₂ : Circle)
    (hce : d.isCentre α₂) (hae : a.onCircle α₂)
    (hdadb : |(d─a)| = |(d─b)|) :
    b.onCircle α₂ := by
  euclid_apply (point_on_circle_if d a b α₂)
  euclid_finish

end Elements.Book3

import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_hcα₂ (a b c d : Point) (α₂ : Circle)
    (hce : d.isCentre α₂) (hae : a.onCircle α₂)
    (hdadb : |(d─a)| = |(d─b)|) (hdbdc : |(d─b)| = |(d─c)|) :
    c.onCircle α₂ := by
  euclid_apply (point_on_circle_if d a c α₂)
  euclid_finish

end Elements.Book3

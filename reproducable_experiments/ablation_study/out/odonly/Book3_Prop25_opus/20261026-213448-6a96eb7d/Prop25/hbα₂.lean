import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_hbα₂ (a b d : Point) (α₂ : Circle)
    (hcen : d.isCentre α₂) (haC : a.onCircle α₂)
    (hdadb : |(d─a)| = |(d─b)|) :
    b.onCircle α₂ := by
  euclid_finish

end Elements.Book3

import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_step20 (d : Point) (α₂ : Circle)
    (hd_centre : d.isCentre α₂) :
    d.isCentre α₂ := by
  exact hd_centre

end Elements.Book3

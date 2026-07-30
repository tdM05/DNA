import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_36_s3 (AH BG : Line)
  (h_par : ¬AH.intersectsLine BG) :
  ¬BG.intersectsLine AH := by
  intro h; exact h_par (intersection_symm BG AH h)

end Elements.Book1

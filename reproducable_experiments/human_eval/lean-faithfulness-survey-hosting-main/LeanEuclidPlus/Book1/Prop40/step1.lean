import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_40_s1 (a d : Point) (AD : Line)
    (haAD : a.onLine AD) (hdAD : d.onLine AD) (had : a ≠ d) :
    distinctPointsOnLine a d AD := by
  exact ⟨haAD, hdAD, had⟩

end Elements.Book1

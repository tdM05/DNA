import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_39_s5_x1
    (a e : Point) (AE : Line)
    (h1 : a.onLine AE) (h2 : e.onLine AE) (h3 : a ≠ e)
    : distinctPointsOnLine a e AE :=
  ⟨h1, h2, h3⟩

end Elements.Book1

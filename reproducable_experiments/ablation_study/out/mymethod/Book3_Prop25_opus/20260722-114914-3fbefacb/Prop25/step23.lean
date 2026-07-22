import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_step23 (b e : Point) (AC DB : Line)
    (hstep22 : e.onLine DB ∧ e.sameSide b AC) : b.sameSide e AC := by
  obtain ⟨_, hess⟩ := hstep22
  euclid_finish

end Elements.Book3

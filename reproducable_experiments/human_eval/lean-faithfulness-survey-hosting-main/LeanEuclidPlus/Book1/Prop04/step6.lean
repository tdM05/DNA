import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_4_s6
  (e f : Point) (BC BC' EF : Line)
  (lineImg : Line → Line)
  (h_ne : lineImg BC ≠ EF)
  (h_lineImg_BC : lineImg BC = BC')
  (s5 : distinctPointsOnLine e f (lineImg BC) ∧ distinctPointsOnLine e f EF)
  : False := by
  rw [h_lineImg_BC] at s5 h_ne
  clear h_lineImg_BC lineImg
  exact h_ne (by euclid_finish)

end Elements.Book1

import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_11_hd_ex (f g h : Point) (ADE : Circle)
    (hg_centre : g.isCentre ADE) (h_out : h.outsideCircle ADE)
    (h_bet_fgh : between f g h) :
    ∃ d : Point, d.onCircle ADE ∧ between g d h := by
  euclid_apply (line_from_points g h) as GH
  euclid_apply (intersection_circle_line_between_points ADE GH g h) as d
  exact ⟨d, by euclid_finish, by euclid_finish⟩

end Elements.Book3

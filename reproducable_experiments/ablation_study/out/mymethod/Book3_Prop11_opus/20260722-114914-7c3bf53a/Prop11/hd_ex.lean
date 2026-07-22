import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_11_hd_ex (g h : Point) (ADE : Circle)
    (hg_centre : g.isCentre ADE) (hh_out : h.outsideCircle ADE) :
    ∃ d : Point, d.onCircle ADE ∧ between g d h := by
  euclid_apply (center_inside_circle g ADE)
  euclid_apply (line_from_points g h) as L
  euclid_apply (intersection_circle_line_between_points ADE L g h) as d
  use d

end Elements.Book3

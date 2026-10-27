import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_11_hd_ex (g h : Point) (ADE : Circle)
  (hg_c : g.isCentre ADE) (hh_out : h.outsideCircle ADE) :
  ∃ d : Point, d.onCircle ADE ∧ between g d h := by
  euclid_apply (center_inside_circle g ADE)
  euclid_apply (line_from_points g h) as GH
  euclid_apply (intersection_circle_line_between_points ADE GH g h) as d
  exact ⟨d, by euclid_finish, by euclid_finish⟩

end Elements.Book3

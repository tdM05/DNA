import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_11_step1 (a f g : Point) (ABC ADE : Circle)
    (h_g_in : g.insideCircle ABC) (h_fg : f ≠ g) (hsuppose1 : ¬between f g a) :
    ∃ h : Point, h ≠ a ∧ h.onCircle ABC ∧ between f g h := by
  euclid_apply (line_from_points g f) as L
  euclid_apply (intersection_circle_line_extending_points ABC L g f) as h
  euclid_finish

end Elements.Book3

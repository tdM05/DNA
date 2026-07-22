import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_11_step1 (a f g : Point) (ABC ADE : Circle)
  (hg_in : g.insideCircle ABC) (hfg : f ≠ g) (hsuppose1 : ¬ between f g a) :
  ∃ h : Point, h ≠ a ∧ h.onCircle ABC ∧ between f g h := by
  euclid_apply (line_from_points g f) as L
  euclid_apply (intersection_circle_line_extending_points ABC L g f) as h
  refine ⟨h, ?_, ?_, ?_⟩
  · intro heq
    subst heq
    apply hsuppose1
    euclid_finish
  · assumption
  · euclid_finish

end Elements.Book3

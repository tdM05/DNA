import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_11_step1 (a f g : Point) (ABC : Circle)
  (hg_in : g.insideCircle ABC) (hf_c : f.isCentre ABC) (hfg : f ≠ g)
  (hsuppose1 : ¬between f g a) :
  ∃ h : Point, h ≠ a ∧ h.onCircle ABC ∧ between f g h := by
  euclid_apply (line_from_points f g) as FG
  euclid_apply (intersection_circle_line_extending_points ABC FG g f) as h
  exact ⟨h, by euclid_finish, by euclid_finish, by euclid_finish⟩

end Elements.Book3

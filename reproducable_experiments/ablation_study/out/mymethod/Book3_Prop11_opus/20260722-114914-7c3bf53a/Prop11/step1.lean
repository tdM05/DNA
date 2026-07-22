import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_11_step1 (a f g : Point) (ABC : Circle)
    (hg_inside : g.insideCircle ABC) (hfg : f ≠ g) (hsuppose : ¬ between f g a) :
    ∃ h : Point, h ≠ a ∧ h.onCircle ABC ∧ between f g h := by
  euclid_apply (line_from_points g f) as L
  euclid_apply (intersection_circle_line_extending_points ABC L g f) as h
  use h
  euclid_finish

end Elements.Book3

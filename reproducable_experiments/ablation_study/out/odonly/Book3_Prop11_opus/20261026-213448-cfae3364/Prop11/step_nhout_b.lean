import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_11_step_nhout_b (a f g h : Point) (ABC ADE : Circle)
    (ha_ABC : a.onCircle ABC) (ha_ADE : a.onCircle ADE)
    (hnoint : ¬ABC.intersectsCircle ADE)
    (hg_in : g.insideCircle ABC) (hf_centre : f.isCentre ABC) (hg_centre : g.isCentre ADE)
    (hfg : f ≠ g) (hga_lt : |(g─a)| < |(f─a)|)
    (h_ne : h ≠ a) (h_on_ABC : h.onCircle ABC) (h_bet_fgh : between f g h)
    (h_on_ADE : h.onCircle ADE) :
    False := by
  -- h on ADE with between f g h forces |f-g| = R - r (internal tangency).
  -- The antipode h' of h through centre f is on ABC and lies outside ADE.
  euclid_apply (line_from_points h f) as HF
  euclid_apply (intersection_circle_line_extending_points ABC HF f h) as h'
  -- h' on ABC, on HF, between h' f h
  have hh'out : h'.outsideCircle ADE := by euclid_finish
  have hint : ABC.intersectsCircle ADE :=
    intersection_circle_circle_1 g h' ABC ADE ⟨by euclid_finish, by euclid_finish, by euclid_finish, hh'out⟩
  exact hnoint hint

end Elements.Book3

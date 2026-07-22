import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_11_step_nhout (a f g h : Point) (ABC ADE : Circle)
  (ha_ABC : a.onCircle ABC) (ha_ADE : a.onCircle ADE)
  (hnint : ¬ ABC.intersectsCircle ADE)
  (hg_in : g.insideCircle ABC)
  (hlt : |(g─a)| < |(f─a)|)
  (hf_c : f.isCentre ABC) (hg_c : g.isCentre ADE)
  (hfg : f ≠ g)
  (hsuppose1 : ¬ between f g a)
  (h_ne : h ≠ a) (h_on_ABC : h.onCircle ABC)
  (h_bet_fgh : between f g h)
  (h_nout : ¬ h.outsideCircle ADE)
  : False := by
  euclid_apply (line_from_points f g) as L
  euclid_apply (center_inside_circle g ADE)
  euclid_apply (intersection_circle_line_2 g ADE L)
  euclid_apply (intersections_circle_line ADE L) as (d1, d2)
  euclid_apply (intersection_circle_line_2 g ABC L)
  euclid_apply (intersections_circle_line ABC L) as (p1, p2)
  euclid_finish

end Elements.Book3

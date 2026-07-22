import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_11_step_nhout (a f g : Point) (ABC ADE : Circle)
    (h_aABC : a.onCircle ABC) (h_aADE : a.onCircle ADE)
    (h_nint : ¬ABC.intersectsCircle ADE)
    (h_gABC : g.insideCircle ABC) (h_gaLT : |(g─a)| < |(f─a)|)
    (h_fc : f.isCentre ABC) (h_gc : g.isCentre ADE) (h_fg : f ≠ g) :
    False := by
  euclid_apply (line_from_points f g) as L
  euclid_apply (intersection_circle_line_extending_points ABC L f g) as k
  -- k : k.onCircle ABC ∧ k.onLine L ∧ between k f g, the far diameter endpoint
  have hkout : k.outsideCircle ADE := by euclid_finish
  euclid_apply (intersection_circle_circle_1 g k ABC ADE)
  euclid_finish

end Elements.Book3

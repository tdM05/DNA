import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_11_step_nhout_a (a f g h : Point) (ABC ADE : Circle)
    (ha_ABC : a.onCircle ABC) (ha_ADE : a.onCircle ADE)
    (hnoint : ¬ABC.intersectsCircle ADE)
    (hg_in : g.insideCircle ABC) (hf_centre : f.isCentre ABC) (hg_centre : g.isCentre ADE)
    (hfg : f ≠ g) (hga_lt : |(g─a)| < |(f─a)|)
    (h_on_ABC : h.onCircle ABC) (h_bet_fgh : between f g h)
    (h_in : h.insideCircle ADE) :
    False := by
  euclid_apply (line_from_points f g) as FG
  euclid_apply (intersections_circle_line ADE FG) as (m1, m2)
  -- m1, m2 : the two points where line FG meets ADE; g lies between them
  have hbtw : between m1 g m2 := by euclid_finish
  -- the point NOT past g from f is the one nearest f, hence inside ABC
  by_cases hb1 : between f g m1
  · -- m1 is the far point, so m2 is the near point and lies inside ABC
    have hm2in : m2.insideCircle ABC := by euclid_finish
    exact hnoint (intersection_circle_circle_2 h m2 ABC ADE h_on_ABC hm2in h_in (by euclid_finish))
  · -- m1 is the near point and lies inside ABC
    have hm1in : m1.insideCircle ABC := by euclid_finish
    exact hnoint (intersection_circle_circle_2 h m1 ABC ADE h_on_ABC hm1in h_in (by euclid_finish))

end Elements.Book3

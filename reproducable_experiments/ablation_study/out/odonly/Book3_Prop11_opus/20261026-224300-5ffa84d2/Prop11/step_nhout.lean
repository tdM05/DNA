import SystemE
import Book3.Prop11.step_nhout_gt
import Book3.Prop11.step_nhout_out
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_11_step_nhout (a f g : Point) (ABC ADE : Circle)
  (ha_ABC : a.onCircle ABC) (ha_ADE : a.onCircle ADE)
  (hni : ¬ ABC.intersectsCircle ADE)
  (hg_in : g.insideCircle ABC)
  (hlt : |(g─a)| < |(f─a)|)
  (hf_c : f.isCentre ABC) (hg_c : g.isCentre ADE)
  (hsuppose1 : ¬ between f g a)
  : False := by
  euclid_apply (line_from_points a f) as AFl
  euclid_apply (center_inside_circle f ABC)
  euclid_apply (intersection_circle_line_extending_points ABC AFl f a) as astar
  have step_nhout_gt : |(g─astar)| > |(g─a)| := by euclid_apply (helper_3_11_step_nhout_gt a f g astar ABC AFl (by euclid_assumption "" (show a.onCircle ABC; assumption)) (by euclid_assumption "" (show astar.onCircle ABC; assumption)) (by euclid_assumption "" (show a.onLine AFl; assumption)) (by euclid_assumption "" (show f.onLine AFl; assumption)) (by euclid_assumption "" (show astar.onLine AFl; assumption)) (by euclid_assumption "" (show between astar f a; assumption)) (by euclid_assumption "" (show f.isCentre ABC; assumption)) (by euclid_assumption "" (show g.insideCircle ABC; assumption)) (by euclid_assumption "" (show |(g─a)| < |(f─a)|; assumption)) (by euclid_assumption "" (show ¬ between f g a; assumption)))
  have step_nhout_out : astar.outsideCircle ADE := by euclid_apply (helper_3_11_step_nhout_out a g astar ADE (by euclid_assumption "" (show a.onCircle ADE; assumption)) (by euclid_assumption "" (show g.isCentre ADE; assumption)) (by euclid_assumption "" (show |(g─astar)| > |(g─a)|; assumption)))
  euclid_apply (intersection_circle_circle_1 g astar ABC ADE)
  euclid_finish

end Elements.Book3

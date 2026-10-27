import SystemE
import Book1.Prop20.Main
import Book3.Prop11.step_nhout_gt_tri
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_11_step_nhout_gt (a f g astar : Point) (ABC : Circle) (AFl : Line)
  (ha_ABC : a.onCircle ABC) (hastar_ABC : astar.onCircle ABC)
  (ha_AFl : a.onLine AFl) (hf_AFl : f.onLine AFl) (hastar_AFl : astar.onLine AFl)
  (hbet : between astar f a)
  (hf_c : f.isCentre ABC)
  (hg_in : g.insideCircle ABC)
  (hlt : |(g─a)| < |(f─a)|)
  (hsuppose1 : ¬ between f g a)
  : |(g─astar)| > |(g─a)| := by
  euclid_apply (line_from_points a g) as AG
  euclid_apply (line_from_points g astar) as GS
  have step_nhout_gt_tri : formTriangle a g astar AG GS AFl := by euclid_apply (helper_3_11_step_nhout_gt_tri a f g astar ABC AG GS AFl (by euclid_assumption "" (show a.onCircle ABC; assumption)) (by euclid_assumption "" (show astar.onCircle ABC; assumption)) (by euclid_assumption "" (show f.isCentre ABC; assumption)) (by euclid_assumption "" (show g.insideCircle ABC; assumption)) (by euclid_assumption "" (show a.onLine AFl; assumption)) (by euclid_assumption "" (show f.onLine AFl; assumption)) (by euclid_assumption "" (show astar.onLine AFl; assumption)) (by euclid_assumption "" (show a.onLine AG; assumption)) (by euclid_assumption "" (show g.onLine AG; assumption)) (by euclid_assumption "" (show g.onLine GS; assumption)) (by euclid_assumption "" (show astar.onLine GS; assumption)) (by euclid_assumption "" (show between astar f a; assumption)) (by euclid_assumption "" (show |(g─a)| < |(f─a)|; assumption)) (by euclid_assumption "" (show ¬ between f g a; assumption)))
  euclid_apply (Elements.Book1.proposition_20 a g astar AG GS AFl)
  euclid_finish

end Elements.Book3

import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_11_step_nhout_gt_tri (a f g astar : Point) (ABC : Circle) (AG GS AFl : Line)
  (ha_ABC : a.onCircle ABC) (hastar_ABC : astar.onCircle ABC)
  (hf_c : f.isCentre ABC) (hg_in : g.insideCircle ABC)
  (ha_AFl : a.onLine AFl) (hf_AFl : f.onLine AFl) (hastar_AFl : astar.onLine AFl)
  (ha_AG : a.onLine AG) (hg_AG : g.onLine AG)
  (hg_GS : g.onLine GS) (hastar_GS : astar.onLine GS)
  (hbet : between astar f a)
  (hlt : |(g─a)| < |(f─a)|)
  (hsuppose1 : ¬ between f g a)
  : formTriangle a g astar AG GS AFl := by
  euclid_finish

end Elements.Book3

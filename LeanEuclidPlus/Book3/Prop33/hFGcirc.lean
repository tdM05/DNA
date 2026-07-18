import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_33_hFGcirc
    (g : Point) (α : Circle) (FG : Line)
    (h_g_centre : g.isCentre α) (h_g_FG : g.onLine FG) :
    FG.intersectsCircle α := by
  euclid_apply (center_inside_circle g α)
  euclid_apply (intersection_circle_line_2 g α FG)
  euclid_finish

end Elements.Book3

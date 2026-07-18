import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_33_hgb
    (a b f g g0 : Point) (AB FG : Line)
    (h_a_AB : a.onLine AB) (h_b_AB : b.onLine AB) (h_afb : between a f b)
    (h_g0_AB : ¬ g0.onLine AB)
    (h_f_FG : f.onLine FG) (h_g0_FG : g0.onLine FG) (h_g_FG : g.onLine FG) :
    g ≠ b := by
  have hbFG : ¬ b.onLine FG := by
    intro hb
    have hdist : distinctPointsOnLine b f FG := by euclid_finish
    euclid_apply (two_points_determine_line b f FG AB)
    euclid_finish
  euclid_finish

end Elements.Book3

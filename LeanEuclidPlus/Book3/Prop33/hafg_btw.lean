import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_33_hafg_btw
    (a b f g g0 : Point) (AB FG : Line)
    (h_a_AB : a.onLine AB) (h_b_AB : b.onLine AB) (h_afb : between a f b)
    (h_afg0 : ∠ a:f:g0 = ∟) (h_g0_AB : ¬ g0.onLine AB)
    (h_f_FG : f.onLine FG) (h_g0_FG : g0.onLine FG)
    (h_g_FG : g.onLine FG) (h_gf : g ≠ f) (h_btw : between g0 f g) :
    ∠ a:f:g = ∟ := by
  have haFG : ¬ a.onLine FG := by
    intro ha
    have hdist : distinctPointsOnLine a f FG := by euclid_finish
    euclid_apply (two_points_determine_line a f FG AB)
    euclid_finish
  euclid_apply (perpendicular_onlyif g0 g f a FG)
  euclid_finish

end Elements.Book3

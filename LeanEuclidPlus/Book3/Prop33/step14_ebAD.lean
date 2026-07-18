import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_33_step14_ebAD
    (a b e e0 : Point) (α : Circle) (AB AD AE : Line)
    (h_ab : a ≠ b) (h_a_AB : a.onLine AB) (h_b_AB : b.onLine AB)
    (h_a_AD : a.onLine AD)
    (h_a_AE : a.onLine AE) (h_e_AE : e.onLine AE) (h_e0_AE : e0.onLine AE)
    (h_e0_AD : ¬ e0.onLine AD)
    (h_a_circ : a.onCircle α) (h_b_circ : b.onCircle α) (h_e_circ : e.onCircle α)
    (h_notint : ¬ AD.intersectsCircle α)
    (h_ABAD : AB ≠ AD) (h_ADAE : AD ≠ AE) (h_ea : e ≠ a) :
    e.sameSide b AD := by
  have hb_AD : ¬ b.onLine AD := by
    intro hbAD
    euclid_apply (two_points_determine_line a b AB AD)
    euclid_finish
  have he_AD : ¬ e.onLine AD := by
    intro heAD
    euclid_apply (two_points_determine_line a e AE AD)
    euclid_finish
  by_contra hcon
  euclid_apply (intersection_circle_line_1 e b α AD)
  euclid_finish

end Elements.Book3

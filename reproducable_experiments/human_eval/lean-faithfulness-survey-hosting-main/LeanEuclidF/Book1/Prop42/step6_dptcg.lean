import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_42_s6_x1 (a b g c : Point) (AB BC AG CG : Line)
    (h_a_AB : a.onLine AB) (h_b_AB : b.onLine AB) (h_a_ne_b : a ≠ b)
    (h_b_BC : b.onLine BC) (h_c_BC : c.onLine BC) (h_AB_ne_BC : AB ≠ BC)
    (h_a_AG : a.onLine AG)
    (h_g_CG : g.onLine CG) (h_c_CG : c.onLine CG)
    (h_g_AG : g.onLine AG)
    (h_par_AG_BC : ¬AG.intersectsLine BC) :
    distinctPointsOnLine g c CG := by
  refine ⟨h_g_CG, h_c_CG, ?_⟩
  intro h_eq

  have h_c_AG : c.onLine AG := h_eq ▸ h_g_AG

  have h_a_not_BC : ¬a.onLine BC := by
    intro h_a_BC
    have h_AB_BC : AB = BC := by
      euclid_apply (two_points_determine_line a b AB BC)
      euclid_finish
    exact h_AB_ne_BC h_AB_BC

  have h_AG_ne_BC : AG ≠ BC := fun h => h_a_not_BC (h ▸ h_a_AG)

  exact h_par_AG_BC (by
    apply intersection_lines_common_point c AG BC
    exact ⟨h_c_AG, h_c_BC, h_AG_ne_BC⟩)

end Elements.Book1

import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_33_he_off
    (a b f g0 e : Point) (α : Circle) (AB FG : Line)
    (h_a_AB : a.onLine AB) (h_b_AB : b.onLine AB) (h_afb : between a f b)
    (h_afg0 : ∠ a:f:g0 = ∟) (h_g0_AB : ¬ g0.onLine AB)
    (h_f_FG : f.onLine FG) (h_g0_FG : g0.onLine FG) (h_e_FG : e.onLine FG)
    (h_e_circ : e.onCircle α) (h_f_centre : f.isCentre α) :
    ¬ e.onLine AB := by
  have hef : e ≠ f := by euclid_finish
  have hf_AB : f.onLine AB := by euclid_finish
  have hAB_FG : AB ≠ FG := by euclid_finish
  intro heAB
  euclid_apply (two_points_determine_line f e AB FG)
  euclid_finish

end Elements.Book3

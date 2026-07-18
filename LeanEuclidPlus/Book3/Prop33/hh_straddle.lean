import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_33_hh_straddle
    (a b f g0 h1 h2 : Point) (α : Circle) (AB FG : Line)
    (h_a_AB : a.onLine AB) (h_b_AB : b.onLine AB) (h_afb : between a f b)
    (h_afg0 : ∠ a:f:g0 = ∟) (h_g0_AB : ¬ g0.onLine AB)
    (h_f_FG : f.onLine FG) (h_g0_FG : g0.onLine FG)
    (h_a_circ : a.onCircle α) (h_b_circ : b.onCircle α)
    (h_h1_circ : h1.onCircle α) (h_h1_FG : h1.onLine FG)
    (h_h2_circ : h2.onCircle α) (h_h2_FG : h2.onLine FG) (h_h1h2 : h1 ≠ h2) :
    h1.opposingSides h2 AB := by
  have hf_in : f.insideCircle α := by euclid_finish
  have hf_AB : f.onLine AB := by euclid_finish
  have hAB_FG : AB ≠ FG := by euclid_finish
  have hh1_off : ¬ h1.onLine AB := by
    intro hh1AB
    euclid_apply (two_points_determine_line f h1 AB FG)
    euclid_finish
  have hh2_off : ¬ h2.onLine AB := by
    intro hh2AB
    euclid_apply (two_points_determine_line f h2 AB FG)
    euclid_finish
  euclid_apply (circle_line_intersections f h1 h2 FG α)
  euclid_apply (pasch_3 h1 f h2 AB)
  euclid_finish

end Elements.Book3

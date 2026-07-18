import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_33_step14_c2
    (a b c1 c2 d0 f : Point) (α : Circle) (AB FG : Line)
    (h_a_AB : a.onLine AB) (h_b_AB : b.onLine AB) (h_afb : between a f b)
    (h_f_FG : f.onLine FG)
    (h_a_circ : a.onCircle α) (h_b_circ : b.onCircle α)
    (h_c1_circ : c1.onCircle α) (h_c1_FG : c1.onLine FG)
    (h_c2_circ : c2.onCircle α) (h_c2_FG : c2.onLine FG) (h_c1c2 : c1 ≠ c2)
    (h_notc1 : ¬ c1.opposingSides d0 AB) (h_d0_off : ¬ d0.onLine AB)
    (h_AB_FG : AB ≠ FG) :
    c2.opposingSides d0 AB := by
  have hf_in : f.insideCircle α := by euclid_finish
  have hf_AB : f.onLine AB := by euclid_finish
  have hc1_off : ¬ c1.onLine AB := by
    intro hc1AB
    euclid_apply (two_points_determine_line f c1 AB FG)
    euclid_finish
  have hc2_off : ¬ c2.onLine AB := by
    intro hc2AB
    euclid_apply (two_points_determine_line f c2 AB FG)
    euclid_finish
  euclid_apply (circle_line_intersections f c1 c2 FG α)
  euclid_apply (pasch_3 c1 f c2 AB)
  euclid_finish

end Elements.Book3

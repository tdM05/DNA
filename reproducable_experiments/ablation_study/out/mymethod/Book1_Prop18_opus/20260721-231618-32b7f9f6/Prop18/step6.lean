import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_18_step6 (a b c d : Point) (AB BC AC : Line)
  (h_a_ab : a.onLine AB) (h_b_ab : b.onLine AB) (h_ab : a ≠ b)
  (h_b_bc : b.onLine BC) (h_c_bc : c.onLine BC)
  (h_a_ac : a.onLine AC) (h_c_ac : c.onLine AC)
  (h_ab_bc : AB ≠ BC) (h_bc_ac : BC ≠ AC) (h_ac_ab : AC ≠ AB)
  (h_adc : between a d c)
  (step5 : ∠ a:b:d > ∠ b:c:a) :
  ∠ a:b:c > ∠ b:c:a := by
  have hd_ab : ¬ d.onLine AB := by euclid_finish
  have hd_bc : ¬ d.onLine BC := by euclid_finish
  euclid_apply (sum_angles_onlyif b a c d AB BC)
  euclid_finish

end Elements.Book1

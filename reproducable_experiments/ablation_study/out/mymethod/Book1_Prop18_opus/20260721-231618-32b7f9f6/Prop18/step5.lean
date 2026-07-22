import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_18_step5 (a b c d : Point) (AC BC : Line)
  (h_a_ac : a.onLine AC) (h_c_ac : c.onLine AC)
  (h_c_bc : c.onLine BC) (h_b_bc : b.onLine BC) (h_bc_ac : BC ≠ AC)
  (h_adc : between a d c)
  (step3 : ∠ a:d:b > ∠ d:c:b)
  (step4 : ∠ a:d:b = ∠ a:b:d) :
  ∠ a:b:d > ∠ b:c:a := by
  have h_ray : ∠ d:c:b = ∠ b:c:a := by euclid_finish
  euclid_finish

end Elements.Book1

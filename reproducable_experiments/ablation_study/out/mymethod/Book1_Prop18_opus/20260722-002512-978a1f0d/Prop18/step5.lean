import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_18_step5 (a b c d : Point) (AB BC AC BD : Line)
    (h_b_BC : b.onLine BC) (h_c_BC : c.onLine BC)
    (h_a_AC : a.onLine AC) (h_c_AC : c.onLine AC)
    (h_adc : between a d c)
    (step3 : ∠ a:d:b > ∠ d:c:b)
    (step4 : ∠ a:d:b = ∠ a:b:d)
    : ∠ a:b:d > ∠ b:c:a := by
  euclid_finish

end Elements.Book1

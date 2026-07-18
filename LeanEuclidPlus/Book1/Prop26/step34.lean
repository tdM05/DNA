import SystemE
import Book1.Prop16.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_26_step34 (a b c h : Point) (AB BC AC AH : Line)
    (h_a_AB : a.onLine AB) (h_b_AB : b.onLine AB)
    (h_b_BC : b.onLine BC) (h_c_BC : c.onLine BC)
    (h_c_AC : c.onLine AC) (h_a_AC : a.onLine AC)
    (h_a_AH : a.onLine AH) (h_h_AH : h.onLine AH)
    (h_AB_BC : AB ≠ BC) (h_BC_AC : BC ≠ AC) (h_AC_AB : AC ≠ AB)
    (h_ab : a ≠ b)
    (h_bhc : between b h c)
    (step33 : ∠ b:h:a = ∠ b:c:a) :
    False := by
  euclid_apply (proposition_16 a c h b AC BC AH)
  euclid_finish

end Elements.Book1

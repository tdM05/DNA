import SystemE
import Book1Variants.Prop05
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_18_step4 (a b c d : Point) (AB BC AC BD : Line)
    (h_a_AB : a.onLine AB) (h_b_AB : b.onLine AB) (h_ab : a ≠ b)
    (h_a_AC : a.onLine AC) (h_c_AC : c.onLine AC)
    (h_b_BD : b.onLine BD) (h_d_BD : d.onLine BD)
    (h_AB_BC : AB ≠ BC) (h_BC_AC : BC ≠ AC) (h_AC_AB : AC ≠ AB)
    (h_bd : distinctPointsOnLine b d BD)
    (h_adc : between a d c)
    (hassump1 : |(a─b)| = |(a─d)|)   -- "$AB$ is also equal to side $AD$"
    : ∠ a:d:b = ∠ a:b:d := by
  euclid_apply (proposition_5' a b d AB BD AC)
  euclid_finish

end Elements.Book1

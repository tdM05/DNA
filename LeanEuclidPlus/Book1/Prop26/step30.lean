import SystemE
import Book1.Prop04.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_26_step30 (a b c d e f h : Point) (AB BC AC AH DE EF DF : Line)
    (h_a_AB : a.onLine AB) (h_b_AB : b.onLine AB)
    (h_b_BC : b.onLine BC) (h_c_BC : c.onLine BC)
    (h_c_AC : c.onLine AC) (h_a_AC : a.onLine AC)
    (h_a_AH : a.onLine AH) (h_h_AH : h.onLine AH)
    (h_AB_BC : AB ≠ BC) (h_BC_AC : BC ≠ AC) (h_AC_AB : AC ≠ AB)
    (h_ab : a ≠ b) (h_de : d ≠ e)
    (h_d_DE : d.onLine DE) (h_e_DE : e.onLine DE)
    (h_e_EF : e.onLine EF) (h_f_EF : f.onLine EF)
    (h_d_DF : d.onLine DF) (h_f_DF : f.onLine DF)
    (h_DE_EF : DE ≠ EF) (h_EF_DF : EF ≠ DF) (h_DF_DE : DF ≠ DE)
    (h_bhc : between b h c)
    (step26 : |(a─b)| = |(d─e)| ∧ |(b─h)| = |(e─f)|)
    (step27 : ∠ a:b:h = ∠ d:e:f) :
    ∠ b:a:h = ∠ e:d:f ∧ ∠ b:h:a = ∠ e:f:d := by
  euclid_apply (proposition_4 b a h e d f AB AH BC DE DF EF)
  euclid_finish

end Elements.Book1

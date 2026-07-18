import SystemE
import Book1.Prop04.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_26_step18 (a b c d e f : Point) (AB BC AC DE EF DF : Line)
    (h_a_AB : a.onLine AB) (h_b_AB : b.onLine AB)
    (h_b_BC : b.onLine BC) (h_c_BC : c.onLine BC)
    (h_c_AC : c.onLine AC) (h_a_AC : a.onLine AC)
    (h_AB_BC : AB ≠ BC) (h_BC_AC : BC ≠ AC) (h_AC_AB : AC ≠ AB)
    (h_ab : a ≠ b) (h_de : d ≠ e)
    (h_d_DE : d.onLine DE) (h_e_DE : e.onLine DE)
    (h_e_EF : e.onLine EF) (h_f_EF : f.onLine EF)
    (h_d_DF : d.onLine DF) (h_f_DF : f.onLine DF)
    (h_DE_EF : DE ≠ EF) (h_EF_DF : EF ≠ DF) (h_DF_DE : DF ≠ DE)
    (step13 : |(a─b)| = |(d─e)|) (step14 : |(b─c)| = |(e─f)|)
    (step16 : ∠ a:b:c = ∠ d:e:f) :
    ∠ b:a:c = ∠ e:d:f := by
  euclid_apply (proposition_4 b a c e d f AB AC BC DE DF EF)
  euclid_finish

end Elements.Book1

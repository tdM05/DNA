import SystemE
import Book1.Prop04.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_26_step7 (a b c d e f g : Point) (AB BC AC GC DE EF DF : Line)
    (h_a_AB : a.onLine AB) (h_b_AB : b.onLine AB)
    (h_b_BC : b.onLine BC) (h_c_BC : c.onLine BC)
    (h_c_AC : c.onLine AC) (h_a_AC : a.onLine AC)
    (h_AB_BC : AB ≠ BC) (h_BC_AC : BC ≠ AC) (h_AC_AB : AC ≠ AB)
    (h_g_GC : g.onLine GC) (h_c_GC : c.onLine GC)
    (h_d_DE : d.onLine DE) (h_e_DE : e.onLine DE)
    (h_e_EF : e.onLine EF) (h_f_EF : f.onLine EF)
    (h_d_DF : d.onLine DF) (h_f_DF : f.onLine DF)
    (h_DE_EF : DE ≠ EF) (h_EF_DF : EF ≠ DF) (h_DF_DE : DF ≠ DE)
    (h_bga : between b g a)
    (step3 : |(g─b)| = |(d─e)| ∧ |(b─c)| = |(e─f)|)
    (step4 : ∠ g:b:c = ∠ d:e:f) :
    ∠ b:g:c = ∠ e:d:f ∧ ∠ g:c:b = ∠ d:f:e := by
  euclid_apply (proposition_4 b g c e d f AB GC BC DE DF EF)
  euclid_finish

end Elements.Book1

import SystemE
import Book1.Prop42.step6_ebc
import Book1.Prop42.step6_dptcg
import Book1.Prop42.step6_same
import Book1.Prop42.step6_par
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_42_s6 (a b e f g c : Point) (AB BC AG EF CG : Line)
    (h_a_AB : a.onLine AB) (h_b_AB : b.onLine AB) (h_a_ne_b : a ≠ b)
    (h_b_BC : b.onLine BC) (h_c_BC : c.onLine BC) (h_AB_ne_BC : AB ≠ BC)
    (h_a_AG : a.onLine AG)
    (h_f_AG : f.onLine AG) (h_f_EF : f.onLine EF)
    (h_g_CG : g.onLine CG) (h_g_AG : g.onLine AG)
    (h_e_EF : e.onLine EF)
    (h_c_CG : c.onLine CG)
    (h_bet : between b e c)
    (h_par_AG_BC : ¬AG.intersectsLine BC)
    (h_par_CG_EF : ¬CG.intersectsLine EF) :
    formParallelogram f g e c AG BC EF CG := by
  have s6_x12 : e.onLine BC := by euclid_apply (h_1_42_s6_x2 b e c BC (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show between b e c; assumption)))
  have s6_x11 : distinctPointsOnLine g c CG := by euclid_apply (h_1_42_s6_x1 a b g c AB BC AG CG (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show AB ≠ BC; assumption)) (by (show a.onLine AG; assumption)) (by (show g.onLine CG; assumption)) (by (show c.onLine CG; assumption)) (by (show g.onLine AG; assumption)) (by (show ¬AG.intersectsLine BC; assumption)))
  have s6_x14 : f.sameSide e CG := by euclid_apply (h_1_42_s6_x4 a b e f g c AB BC AG EF CG (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show AB ≠ BC; assumption)) (by (show a.onLine AG; assumption)) (by (show f.onLine EF; assumption)) (by (show f.onLine AG; assumption)) (by (show e.onLine EF; assumption)) (by (show e.onLine BC; assumption)) (by (show g.onLine CG; assumption)) (by (show c.onLine CG; assumption)) (by (show c.onLine BC; assumption)) (by (show between b e c; assumption)) (by (show ¬AG.intersectsLine BC; assumption)) (by (show ¬CG.intersectsLine EF; assumption)))
  have s6_x13 : ¬EF.intersectsLine CG := by euclid_apply (h_1_42_s6_x3 EF CG (by (show ¬CG.intersectsLine EF; assumption)))
  exact ⟨h_f_AG, h_g_AG, s6_x12, h_c_BC, h_f_EF, h_e_EF, s6_x11, s6_x14, h_par_AG_BC, s6_x13⟩

end Elements.Book1

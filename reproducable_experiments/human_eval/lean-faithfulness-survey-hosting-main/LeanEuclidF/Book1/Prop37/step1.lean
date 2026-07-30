import SystemE
import Book1.Prop37.step1_dae
import Book1.Prop37.step1_adf
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_37_s1 (a b c d e f : Point) (AB BC AC BD CD AD BE CF : Line)
    (h_a_AB : a.onLine AB) (h_b_AB : b.onLine AB) (h_ab : a ≠ b)
    (h_b_BC : b.onLine BC) (h_c_BC : c.onLine BC)
    (h_c_AC : c.onLine AC) (h_a_AC : a.onLine AC)
    (h_AB_BC : AB ≠ BC) (h_BC_AC : BC ≠ AC) (h_AC_AB : AC ≠ AB)
    (h_d_BD : d.onLine BD) (h_b_BD : b.onLine BD) (h_db : d ≠ b)
    (h_c_CD : c.onLine CD) (h_d_CD : d.onLine CD)
    (h_BD_BC : BD ≠ BC) (h_BC_CD : BC ≠ CD) (h_CD_BD : CD ≠ BD)
    (h_a_AD : a.onLine AD) (h_d_AD : d.onLine AD) (h_ad : a ≠ d)
    (h_AD_BC : ¬AD.intersectsLine BC) (h_dc_AB : d.sameSide c AB)
    (h_b_BE : b.onLine BE) (h_BE_AC : ¬BE.intersectsLine AC)
    (h_e_AD : e.onLine AD) (h_e_BE : e.onLine BE)
    (h_c_CF : c.onLine CF) (h_CF_BD : ¬CF.intersectsLine BD)
    (h_f_AD : f.onLine AD) (h_f_CF : f.onLine CF) :
    between d a e ∧ between a d f := by
  have s1_x5 : between d a e := by euclid_apply (h_1_37_s1_x2 a b c d e AB BC AC AD BE (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show c.onLine AC; assumption)) (by (show a.onLine AC; assumption)) (by (show AB ≠ BC; assumption)) (by (show BC ≠ AC; assumption)) (by (show AC ≠ AB; assumption)) (by (show a.onLine AD; assumption)) (by (show d.onLine AD; assumption)) (by (show a ≠ d; assumption)) (by (show ¬AD.intersectsLine BC; assumption)) (by (show d.sameSide c AB; assumption)) (by (show b.onLine BE; assumption)) (by (show ¬BE.intersectsLine AC; assumption)) (by (show e.onLine AD; assumption)) (by (show e.onLine BE; assumption)))
  have s1_x1 : between a d f := by euclid_apply (h_1_37_s1_x1 a b c d f AB BC BD CD AD CF (by (show b.onLine AB; assumption)) (by (show a.onLine AB; assumption)) (by (show d.onLine BD; assumption)) (by (show b.onLine BD; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show c.onLine CD; assumption)) (by (show d.onLine CD; assumption)) (by (show BD ≠ BC; assumption)) (by (show BC ≠ CD; assumption)) (by (show CD ≠ BD; assumption)) (by (show a.onLine AD; assumption)) (by (show d.onLine AD; assumption)) (by (show a ≠ d; assumption)) (by (show ¬AD.intersectsLine BC; assumption)) (by (show d.sameSide c AB; assumption)) (by (show c.onLine CF; assumption)) (by (show ¬CF.intersectsLine BD; assumption)) (by (show f.onLine AD; assumption)) (by (show f.onLine CF; assumption)))
  exact ⟨s1_x5, s1_x1⟩

end Elements.Book1

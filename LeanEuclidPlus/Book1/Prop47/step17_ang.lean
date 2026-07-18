import SystemE
import Mathlib.Tactic.Linarith
import Helpers.Parallel
import Helpers.SameSide
import Book1.Prop47.step17_koffBC
import Book1.Prop47.step8_agBC
import Book1.Prop47.step8_ahBC
import Book1.Prop47.step17_agCK
import Book1.Prop47.step17_agCE
import Book1.Prop47.step17_hkAC
import Book1.Prop47.step8_bcAL
import Book1.Prop47.step8_dle
import Book1.Prop47.step17_B
import Book1.Prop47.step17_A
import Book1.Prop47.step17_D
import Book1.Prop47.step17_C
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

-- Mirror of step8 (windmill angle-equality) for the AC-leg: b↔c, d↔e, f↔k, g↔h, BD↔CE, BF↔CK,
-- GF↔HK, AG↔AH, AB↔AC. `¬b.sameSide c AL` and `between d l e` are b↔c-symmetric ⟹ REUSED.
theorem helper_1_47_step17_ang
    (a b c d e f g h k l : Point) (AB BC BD BF CE CK DE GF HK AG AH AC AL : Line)
    (hbAB : b.onLine AB) (haAB : a.onLine AB)
    (hcBC : c.onLine BC) (hbBC : b.onLine BC)
    (hcCE : c.onLine CE) (heCE : e.onLine CE)
    (haAC : a.onLine AC) (hcAC : c.onLine AC)
    (hcCK : c.onLine CK) (hkCK : k.onLine CK)
    (hdDE : d.onLine DE) (heDE : e.onLine DE) (hlDE : l.onLine DE)
    (hhHK : h.onLine HK) (hkHK : k.onLine HK)
    (hbBD : b.onLine BD) (hdBD : d.onLine BD)
    (haAL : a.onLine AL) (hlAL : l.onLine AL)
    (haAH : a.onLine AH) (hhAH : h.onLine AH)
    (hbac : ∠ b:a:c = ∟) (hbce : ∠ b:c:e = ∟) (hack : ∠ a:c:k = ∟) (hcbd : ∠ c:b:d = ∟)
    (hhaCK : h.sameSide a CK) (hhbAC : ¬h.sameSide b AC) (hdaBC : ¬d.sameSide a BC)
    (hdbCE : d.sameSide b CE)
    (hcag : between c a g) (hbah : between b a h)
    (hALBD : ¬AL.intersectsLine BD) (hAHCK : ¬AH.intersectsLine CK)
    (hHKAC : ¬HK.intersectsLine AC) (hDEBC : ¬DE.intersectsLine BC) (hBDCE : ¬BD.intersectsLine CE)
    (hboffAC : ¬b.onLine AC) (haoffBC : ¬a.onLine BC) (hdoffBC : ¬d.onLine BC)
    (hhoffAC : ¬h.onLine AC) (haoffBD : ¬a.onLine BD)
    (hec : e ≠ c) (hkc : k ≠ c) (hbdlen : |(b─d)| = |(b─c)|) (hcelen : |(c─e)| = |(b─c)|) :
    ∠ e:c:a = ∠ k:c:b := by
  have hcb : c ≠ b := by euclid_finish
  have hbc : b ≠ c := Ne.symm hcb
  have hce : c ≠ e := by euclid_finish
  have hab : a ≠ b := by euclid_finish
  have hac : a ≠ c := by euclid_finish
  have haoffCE : ¬a.onLine CE := by euclid_finish
  have hcoffAL : ¬c.onLine AL := by euclid_finish
  have hbd : b ≠ d := by euclid_finish
  have hde : d ≠ e := by euclid_finish
  have hdl : d ≠ l := by euclid_finish
  have hel : e ≠ l := by euclid_finish
  have hALDE : AL ≠ DE := by euclid_finish
  have hALCE : ¬AL.intersectsLine CE := by
    euclid_apply (Elements.not_intersects_trans AL BD CE)
    euclid_finish
  have hDEBC_ne : DE ≠ BC := by euclid_finish
  have hdeBC : d.sameSide e BC := by
    euclid_apply (Elements.sameSide_of_parallel_both d e DE BC hdDE heDE hDEBC_ne hDEBC)
  have headBC : ¬e.sameSide a BC := by euclid_finish
  have hAB_ne_AC : AB ≠ AC := by euclid_finish
  have hCK_ne_AC : CK ≠ AC := by euclid_finish
  have haoffCK : ¬a.onLine CK := by euclid_finish
  have hACBC : AC ≠ BC := by euclid_finish
  have hBCAB : BC ≠ AB := by euclid_finish
  have step17_koffBC : ¬k.onLine BC := by euclid_apply (helper_1_47_step17_koffBC a b c k AC BC AB (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show AC ≠ BC; assumption)) (by euclid_assumption "" (show BC ≠ AB; assumption)) (by euclid_assumption "" (show AB ≠ AC; assumption)) (by euclid_assumption "" (show ∠ b:a:c = ∟; assumption)) (by euclid_assumption "" (show ∠ a:c:k = ∟; assumption)) (by euclid_assumption "" (show ¬a.onLine BC; assumption)) (by euclid_assumption "" (show k ≠ c; assumption)) (by euclid_assumption "" (show b ≠ c; assumption)))
  have hCKBC : CK ≠ BC := fun h => step17_koffBC (h ▸ hkCK)
  have hboffCK : ¬b.onLine CK := by euclid_finish
  -- BC seeds (reused, symmetric)
  have step8_agBC : a.sameSide g BC := by euclid_apply (helper_1_47_step8_agBC a c g BC (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show ¬a.onLine BC; assumption)) (by euclid_assumption "" (show between c a g; assumption)))
  have step8_ahBC : a.sameSide h BC := by euclid_apply (helper_1_47_step8_ahBC a b h BC (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show ¬a.onLine BC; assumption)) (by euclid_assumption "" (show between b a h; assumption)))
  -- CK / CE seeds (mirror ahBF / ahBD)
  have step17_agCK : a.sameSide g CK := by euclid_apply (helper_1_47_step17_agCK a c g CK (by euclid_assumption "" (show c.onLine CK; assumption)) (by euclid_assumption "" (show ¬a.onLine CK; assumption)) (by euclid_assumption "" (show between c a g; assumption)))
  have step17_agCE : a.sameSide g CE := by euclid_apply (helper_1_47_step17_agCE a c g CE (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show ¬a.onLine CE; assumption)) (by euclid_assumption "" (show between c a g; assumption)))
  have step17_hkAC : h.sameSide k AC := by euclid_apply (helper_1_47_step17_hkAC h k HK AC (by euclid_assumption "" (show h.onLine HK; assumption)) (by euclid_assumption "" (show k.onLine HK; assumption)) (by euclid_assumption "" (show ¬h.onLine AC; assumption)) (by euclid_assumption "" (show ¬HK.intersectsLine AC; assumption)))
  have hkbAC : ¬k.sameSide b AC := by euclid_finish
  have hACAB : AC ≠ AB := Ne.symm hAB_ne_AC
  have hBCAC : BC ≠ AC := Ne.symm hACBC
  have hABBC : AB ≠ BC := Ne.symm hBCAB
  have step8_bcAL : ¬b.sameSide c AL := by euclid_apply (helper_1_47_step8_bcAL a b c d AL BD BC AB AC (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show AB ≠ BC; assumption)) (by euclid_assumption "" (show BC ≠ AC; assumption)) (by euclid_assumption "" (show AC ≠ AB; assumption)) (by euclid_assumption "" (show ∠ b:a:c = ∟; assumption)) (by euclid_assumption "" (show a.onLine AL; assumption)) (by euclid_assumption "" (show ¬AL.intersectsLine BD; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show ∠ c:b:d = ∟; assumption)) (by euclid_assumption "" (show ¬d.sameSide a BC; assumption)) (by euclid_assumption "" (show ¬d.onLine BC; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show a ≠ c; assumption)) (by euclid_assumption "" (show b ≠ c; assumption)) (by euclid_assumption "" (show b ≠ d; assumption)) (by euclid_assumption "" (show ¬a.onLine BC; assumption)) (by euclid_assumption "" (show ¬a.onLine BD; assumption)))
  have step8_dle : between d l e := by euclid_apply (helper_1_47_step8_dle a b c d e l AL BD CE DE (by euclid_assumption "" (show a.onLine AL; assumption)) (by euclid_assumption "" (show l.onLine AL; assumption)) (by euclid_assumption "" (show l.onLine DE; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show e.onLine CE; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show ¬AL.intersectsLine BD; assumption)) (by euclid_assumption "" (show ¬BD.intersectsLine CE; assumption)) (by euclid_assumption "" (show ¬a.onLine BD; assumption)) (by euclid_assumption "" (show d.sameSide b CE; assumption)) (by euclid_assumption "" (show ¬b.sameSide c AL; assumption)) (by euclid_assumption "" (show d ≠ l; assumption)) (by euclid_assumption "" (show e ≠ l; assumption)) (by euclid_assumption "" (show d ≠ e; assumption)) (by euclid_assumption "" (show AL ≠ DE; assumption)))
  have step17_B : a.sameSide b CE := by euclid_apply (helper_1_47_step17_B a b d e l CE AL DE (by euclid_assumption "" (show a.onLine AL; assumption)) (by euclid_assumption "" (show l.onLine AL; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show l.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine CE; assumption)) (by euclid_assumption "" (show ¬AL.intersectsLine CE; assumption)) (by euclid_assumption "" (show ¬a.onLine CE; assumption)) (by euclid_assumption "" (show d.sameSide b CE; assumption)) (by euclid_assumption "" (show between d l e; assumption)))
  have step17_A : e.sameSide b AC := by euclid_apply (helper_1_47_step17_A a b c e CE BC AC (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e.onLine CE; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show a.sameSide b CE; assumption)) (by euclid_assumption "" (show ¬e.sameSide a BC; assumption)) (by euclid_assumption "" (show ¬a.onLine BC; assumption)) (by euclid_assumption "" (show e ≠ c; assumption)))
  have hAB_ne_CK : AB ≠ CK := by euclid_finish
  have hcab : ∠ c:a:b = ∟ := by
    euclid_apply (angle_symm c a b)
    euclid_finish
  have step17_D : b.sameSide a CK := by euclid_apply (helper_1_47_step17_D a b c k AB BC CK AC (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine CK; assumption)) (by euclid_assumption "" (show k.onLine CK; assumption)) (by euclid_assumption "" (show ∠ c:a:b = ∟; assumption)) (by euclid_assumption "" (show ∠ a:c:k = ∟; assumption)) (by euclid_assumption "" (show ¬a.onLine CK; assumption)) (by euclid_assumption "" (show ¬b.onLine CK; assumption)) (by euclid_assumption "" (show AB ≠ AC; assumption)) (by euclid_assumption "" (show CK ≠ AC; assumption)) (by euclid_assumption "" (show AB ≠ CK; assumption)) (by euclid_assumption "" (show a ≠ c; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show k ≠ c; assumption)))
  have step17_C : k.sameSide a BC := by euclid_apply (helper_1_47_step17_C a b c k CK AC BC (by euclid_assumption "" (show c.onLine CK; assumption)) (by euclid_assumption "" (show k.onLine CK; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show b.sameSide a CK; assumption)) (by euclid_assumption "" (show ¬k.sameSide b AC; assumption)) (by euclid_assumption "" (show ¬b.onLine AC; assumption)) (by euclid_assumption "" (show k ≠ c; assumption)))
  euclid_apply (sum_angles_onlyif c e a b CE AC)
  euclid_apply (sum_angles_onlyif c k b a CK BC)
  euclid_apply (angle_symm b c a)
  euclid_apply (angle_symm e c b)
  euclid_apply (angle_symm k c a)
  linarith

end Elements.Book1

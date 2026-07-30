import SystemE
import Book1.Prop47.step17_hacuteC
import Book1.Prop47.step17_ss_aCE
import Book1.Prop47.step17_ss_bCK
import Book1.Prop47.step17_ne_same
import Book1.Prop47.step17_nk_same
import Book1.Prop47.step17_ss_eAC
import Book1.Prop47.step17_ss_kBC
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_47_s17_x10
    (a b c d e h k : Point) (AB AC CE CK BC DE HK : Line)
    (ha_AB : a.onLine AB) (hb_AB : b.onLine AB) (hab : a ≠ b)
    (hb_BC : b.onLine BC) (hc_BC : c.onLine BC) (hcb : c ≠ b)
    (ha_AC : a.onLine AC) (hc_AC : c.onLine AC) (hca : c ≠ a)
    (hc_CE : c.onLine CE) (he_CE : e.onLine CE) (hce : c ≠ e)
    (hc_CK : c.onLine CK) (hk_CK : k.onLine CK) (hck : c ≠ k)
    (hd_DE : d.onLine DE) (he_DE : e.onLine DE)
    (hh_HK : h.onLine HK) (hk_HK : k.onLine HK)
    (hABBC : AB ≠ BC) (hBCAC : BC ≠ AC) (hACAB : AC ≠ AB)
    (hBCCE : BC ≠ CE) (hACCK : AC ≠ CK)
    (h_a_nBC : ¬a.onLine BC) (h_b_nAC : ¬b.onLine AC)
    (h_d_nBC : ¬d.onLine BC) (h_e_nBC : ¬e.onLine BC)
    (h_h_nAC : ¬h.onLine AC) (h_k_nAC : ¬k.onLine AC)
    (h_a_nCE : ¬a.onLine CE) (h_b_nCK : ¬b.onLine CK)
    (h_b_nCE : ¬b.onLine CE) (h_a_nCK : ¬a.onLine CK)
    (h_nDEBC : ¬DE.intersectsLine BC) (h_nHKAC : ¬HK.intersectsLine AC)
    (h_nd_same_a_BC : ¬d.sameSide a BC) (h_nh_same_b_AC : ¬h.sameSide b AC)
    (h_bce : (∠ b:c:e : ℝ) = ∟) (h_ack : (∠ a:c:k : ℝ) = ∟)
    (h_bac : (∠ b:a:c : ℝ) = ∟) :
    ∠ e:c:a = ∠ b:c:k := by
  have s17_x8 : (∠ a:c:b : ℝ) < ∟ := by euclid_apply (h_1_47_s17_x6 a b c AB BC AC (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show a.onLine AC; assumption)) (by (show c.onLine AC; assumption)) (by (show AB ≠ BC; assumption)) (by (show BC ≠ AC; assumption)) (by (show AC ≠ AB; assumption)) (by (show (∠ b:a:c : ℝ) = ∟; assumption)))
  have s17_x15 : a.sameSide b CE := by euclid_apply (h_1_47_s17_x13 a b c e BC CE (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show c ≠ b; assumption)) (by (show c.onLine CE; assumption)) (by (show e.onLine CE; assumption)) (by (show c ≠ e; assumption)) (by (show BC ≠ CE; assumption)) (by (show ¬a.onLine BC; assumption)) (by (show ¬a.onLine CE; assumption)) (by (show (∠ b:c:e : ℝ) = ∟; assumption)) (by (show (∠ a:c:b : ℝ) < ∟; assumption)))
  have s17_x16 : b.sameSide a CK := by euclid_apply (h_1_47_s17_x14 a b c k AC CK (by (show a.onLine AC; assumption)) (by (show c.onLine AC; assumption)) (by (show c ≠ a; assumption)) (by (show c.onLine CK; assumption)) (by (show k.onLine CK; assumption)) (by (show c ≠ k; assumption)) (by (show AC ≠ CK; assumption)) (by (show ¬b.onLine AC; assumption)) (by (show ¬b.onLine CK; assumption)) (by (show (∠ a:c:k : ℝ) = ∟; assumption)) (by (show (∠ a:c:b : ℝ) < ∟; assumption)))
  have s17_x9 : ¬e.sameSide a BC := by euclid_apply (h_1_47_s17_x7 a d e BC DE (by (show d.onLine DE; assumption)) (by (show e.onLine DE; assumption)) (by (show ¬DE.intersectsLine BC; assumption)) (by (show ¬d.onLine BC; assumption)) (by (show ¬e.onLine BC; assumption)) (by (show ¬a.onLine BC; assumption)) (by (show ¬d.sameSide a BC; assumption)))
  have s17_x10 : ¬k.sameSide b AC := by euclid_apply (h_1_47_s17_x8 b h k AC HK (by (show h.onLine HK; assumption)) (by (show k.onLine HK; assumption)) (by (show ¬HK.intersectsLine AC; assumption)) (by (show ¬h.onLine AC; assumption)) (by (show ¬k.onLine AC; assumption)) (by (show ¬b.onLine AC; assumption)) (by (show ¬h.sameSide b AC; assumption)))
  have s17_x17 : e.sameSide b AC := by euclid_apply (h_1_47_s17_x15 a b c e CE BC AC (by (show c.onLine CE; assumption)) (by (show c.onLine BC; assumption)) (by (show c.onLine AC; assumption)) (by (show e.onLine CE; assumption)) (by (show b.onLine BC; assumption)) (by (show a.onLine AC; assumption)) (by (show c ≠ e; assumption)) (by (show ¬a.onLine BC; assumption)) (by (show ¬e.sameSide a BC; assumption)) (by (show a.sameSide b CE; assumption)))
  have s17_x18 : k.sameSide a BC := by euclid_apply (h_1_47_s17_x16 a b c k CK AC BC (by (show c.onLine CK; assumption)) (by (show c.onLine AC; assumption)) (by (show c.onLine BC; assumption)) (by (show k.onLine CK; assumption)) (by (show a.onLine AC; assumption)) (by (show b.onLine BC; assumption)) (by (show c ≠ k; assumption)) (by (show ¬b.onLine AC; assumption)) (by (show ¬k.sameSide b AC; assumption)) (by (show b.sameSide a CK; assumption)))
  euclid_apply (sum_angles_onlyif c e a b CE AC)
  euclid_apply (sum_angles_onlyif c k b a CK BC)
  euclid_finish

end Elements.Book1

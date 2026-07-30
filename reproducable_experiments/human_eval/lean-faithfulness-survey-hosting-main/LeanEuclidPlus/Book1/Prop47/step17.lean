import SystemE
import Book1.Prop17.Main
import Book1.Prop47.step17_sas_angle
import Book1.Prop47.step17_sas
import Book1.Prop47.step17_CL
import Book1.Prop47.step17_HC
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_47_s17
    (a b c d e h k l m : Point) (AB AC AL AE BK CE DE BC BD AH CK HK : Line)
    (ha_AB : a.onLine AB) (hb_AB : b.onLine AB) (hab : a ≠ b)
    (ha_AL : a.onLine AL) (hm_AL : m.onLine AL) (hl_AL : l.onLine AL)
    (hc_CE : c.onLine CE) (he_CE : e.onLine CE)
    (hm_BC : m.onLine BC) (hc_BC : c.onLine BC) (hb_BC : b.onLine BC)
    (hl_DE : l.onLine DE) (he_DE : e.onLine DE) (hd_DE : d.onLine DE)
    (ha_AE : a.onLine AE) (he_AE : e.onLine AE)
    (ha_AC : a.onLine AC) (hc_AC : c.onLine AC)
    (ha_AH : a.onLine AH) (hh_AH : h.onLine AH)
    (hc_CK : c.onLine CK) (hk_CK : k.onLine CK)
    (hh_HK : h.onLine HK) (hk_HK : k.onLine HK)
    (hb_BK : b.onLine BK) (hk_BK : k.onLine BK)
    (hb_BD : b.onLine BD) (hoffBD : ¬a.onLine BD)
    (hABBC : AB ≠ BC) (hBCAC : BC ≠ AC) (hACAB : AC ≠ AB)
    (h_a_nBC : ¬a.onLine BC) (h_b_nAC : ¬b.onLine AC)
    (h_d_nBC : ¬d.onLine BC)
    (h_h_nAC : ¬h.onLine AC)
    (h_nDEBC : ¬DE.intersectsLine BC) (h_nALBD : ¬AL.intersectsLine BD)
    (h_nBDCE : ¬BD.intersectsLine CE)
    (h_nAHCK : ¬AH.intersectsLine CK) (h_nHKAC : ¬HK.intersectsLine AC)
    (h_bah : between b a h)
    (hce_len : |(c─e)| = |(b─c)|) (hck_len : |(c─k)| = |(a─c)|)
    (h_bce : (∠ b:c:e : ℝ) = ∟) (h_ack : (∠ a:c:k : ℝ) = ∟)
    (h_bac : (∠ b:a:c : ℝ) = ∟)
    (h_nd_same_a_BC : ¬d.sameSide a BC) (h_nh_same_b_AC : ¬h.sameSide b AC) :
    Triangle.area △ c:e:l + Triangle.area △ c:l:m = Triangle.area △ a:h:k + Triangle.area △ a:k:c := by
  have hac : a ≠ c := by euclid_finish
  have hcb : c ≠ b := by euclid_finish
  have hca : c ≠ a := by euclid_finish
  have hce : c ≠ e := by euclid_finish
  have hck : c ≠ k := by euclid_finish
  have h_c_nBD : ¬c.onLine BD := by euclid_finish
  euclid_apply (proposition_17 b c a BC AC AB)
  have hacuteC : (∠ a:c:b : ℝ) < ∟ := by euclid_finish
  have h_e_nBC : ¬e.onLine BC := by euclid_finish
  have h_k_nAC : ¬k.onLine AC := by euclid_finish
  have hBCCE : BC ≠ CE := by euclid_finish
  have hACCK : AC ≠ CK := by euclid_finish
  have h_offCE : ¬a.onLine CE := by euclid_finish
  have h_b_nCE : ¬b.onLine CE := by euclid_finish
  have h_a_nCK : ¬a.onLine CK := by euclid_finish
  have h_b_nCK : ¬b.onLine CK := by euclid_finish
  have h_k_nBC : ¬k.onLine BC := by euclid_finish
  have s17_x12 : ∠ e:c:a = ∠ b:c:k := by euclid_apply (h_1_47_s17_x10 a b c d e h k AB AC CE CK BC DE HK (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show c ≠ b; assumption)) (by (show a.onLine AC; assumption)) (by (show c.onLine AC; assumption)) (by (show c ≠ a; assumption)) (by (show c.onLine CE; assumption)) (by (show e.onLine CE; assumption)) (by (show c ≠ e; assumption)) (by (show c.onLine CK; assumption)) (by (show k.onLine CK; assumption)) (by (show c ≠ k; assumption)) (by (show d.onLine DE; assumption)) (by (show e.onLine DE; assumption)) (by (show h.onLine HK; assumption)) (by (show k.onLine HK; assumption)) (by (show AB ≠ BC; assumption)) (by (show BC ≠ AC; assumption)) (by (show AC ≠ AB; assumption)) (by (show BC ≠ CE; assumption)) (by (show AC ≠ CK; assumption)) (by (show ¬a.onLine BC; assumption)) (by (show ¬b.onLine AC; assumption)) (by (show ¬d.onLine BC; assumption)) (by (show ¬e.onLine BC; assumption)) (by (show ¬h.onLine AC; assumption)) (by (show ¬k.onLine AC; assumption)) (by (show ¬a.onLine CE; assumption)) (by (show ¬b.onLine CK; assumption)) (by (show ¬b.onLine CE; assumption)) (by (show ¬a.onLine CK; assumption)) (by (show ¬DE.intersectsLine BC; assumption)) (by (show ¬HK.intersectsLine AC; assumption)) (by (show ¬d.sameSide a BC; assumption)) (by (show ¬h.sameSide b AC; assumption)) (by (show (∠ b:c:e : ℝ) = ∟; assumption)) (by (show (∠ a:c:k : ℝ) = ∟; assumption)) (by (show (∠ b:a:c : ℝ) = ∟; assumption)))
  have s17_x11 : Triangle.area △ a:c:e = Triangle.area △ c:b:k := by euclid_apply (h_1_47_s17_x9 a b c e k CE AE AC BC BK CK (by (show c.onLine CE; assumption)) (by (show e.onLine CE; assumption)) (by (show a.onLine AE; assumption)) (by (show e.onLine AE; assumption)) (by (show a.onLine AC; assumption)) (by (show c.onLine AC; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show b.onLine BK; assumption)) (by (show k.onLine BK; assumption)) (by (show c.onLine CK; assumption)) (by (show k.onLine CK; assumption)) (by (show |(c─e)| = |(b─c)|; assumption)) (by (show |(c─k)| = |(a─c)|; assumption)) (by (show ∠ e:c:a = ∠ b:c:k; assumption)) (by (show ¬a.onLine CE; assumption)) (by (show ¬k.onLine BC; assumption)) (by (show c ≠ b; assumption)) (by (show c ≠ a; assumption)))
  have s17_x2 : Triangle.area △ c:e:l + Triangle.area △ c:l:m =
      Triangle.area △ a:c:e + Triangle.area △ a:c:e := by euclid_apply (h_1_47_s17_x2 a b c e l m AC CE BC DE AL AE BD (by (show m.onLine AL; assumption)) (by (show l.onLine AL; assumption)) (by (show a.onLine AL; assumption)) (by (show c.onLine CE; assumption)) (by (show e.onLine CE; assumption)) (by (show m.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show l.onLine DE; assumption)) (by (show e.onLine DE; assumption)) (by (show a.onLine AC; assumption)) (by (show c.onLine AC; assumption)) (by (show a.onLine AE; assumption)) (by (show e.onLine AE; assumption)) (by (show ¬a.onLine CE; assumption)) (by (show ¬a.onLine BD; assumption)) (by (show b.onLine BD; assumption)) (by (show b.onLine BC; assumption)) (by (show ¬c.onLine BD; assumption)) (by (show ¬e.onLine BC; assumption)) (by (show ¬DE.intersectsLine BC; assumption)) (by (show ¬AL.intersectsLine BD; assumption)) (by (show ¬BD.intersectsLine CE; assumption)))
  have s17_x4 : Triangle.area △ a:h:k + Triangle.area △ a:k:c =
      Triangle.area △ c:b:k + Triangle.area △ c:b:k := by euclid_apply (h_1_47_s17_x4 a b c h k AC AH CK HK BK BC (by (show h.onLine AH; assumption)) (by (show a.onLine AH; assumption)) (by (show k.onLine CK; assumption)) (by (show c.onLine CK; assumption)) (by (show h.onLine HK; assumption)) (by (show k.onLine HK; assumption)) (by (show a.onLine AC; assumption)) (by (show c.onLine AC; assumption)) (by (show a ≠ c; assumption)) (by (show b.onLine BK; assumption)) (by (show k.onLine BK; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show ¬h.onLine AC; assumption)) (by (show ¬AH.intersectsLine CK; assumption)) (by (show ¬HK.intersectsLine AC; assumption)) (by (show between b a h; assumption)))
  euclid_finish

end Elements.Book1

import SystemE
import Book1.Prop17.Main
import Book1.Prop47.step17_ALCE
import Book1.Prop47.step17_ne_same
import Book1.Prop47.step18_bdec
import Book1.Prop47.step17_CL_pgram
import Book1.Prop47.step18_perp
import Book1.Prop47.step18_perpc
import Book1.Prop47.step18_blc
import Book1.Prop47.step18_dle
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_47_s18
    (a b c d e f g h k l m : Point) (AB BC AC DE BD CE AL : Line)
    (ha_AB : a.onLine AB) (hb_AB : b.onLine AB) (hab : a ≠ b)
    (hb_BC : b.onLine BC) (hc_BC : c.onLine BC)
    (ha_AC : a.onLine AC) (hc_AC : c.onLine AC)
    (hd_DE : d.onLine DE) (he_DE : e.onLine DE)
    (hb_BD : b.onLine BD) (hd_BD : d.onLine BD)
    (hc_CE : c.onLine CE) (he_CE : e.onLine CE)
    (ha_AL : a.onLine AL) (hm_AL : m.onLine AL) (hm_BC : m.onLine BC)
    (hl_AL : l.onLine AL) (hl_DE : l.onLine DE)
    (hABBC : AB ≠ BC) (hBCAC : BC ≠ AC) (hACAB : AC ≠ AB)
    (hoffBD : ¬a.onLine BD) (h_a_nBC : ¬a.onLine BC) (h_d_nBC : ¬d.onLine BC)
    (h_cbd : (∠ c:b:d : ℝ) = ∟) (h_bce : (∠ b:c:e : ℝ) = ∟) (h_bac : (∠ b:a:c : ℝ) = ∟)
    (h_nd_same_a_BC : ¬d.sameSide a BC)
    (h_nDEBC : ¬DE.intersectsLine BC) (h_nBDCE : ¬BD.intersectsLine CE)
    (h_nALBD : ¬AL.intersectsLine BD)
    (s16 : Triangle.area △ b:m:l + Triangle.area △ b:l:d =
      Triangle.area △ a:g:f + Triangle.area △ a:f:b)
    (s17 : Triangle.area △ c:e:l + Triangle.area △ c:l:m =
      Triangle.area △ a:h:k + Triangle.area △ a:k:c) :
    Triangle.area △ b:d:e + Triangle.area △ b:e:c =
      (Triangle.area △ a:g:f + Triangle.area △ a:f:b) +
      (Triangle.area △ a:h:k + Triangle.area △ a:k:c) := by
  have hac : a ≠ c := by euclid_finish
  euclid_apply (proposition_17 b c a BC AC AB)
  have hacuteC : (∠ a:c:b : ℝ) < ∟ := by euclid_finish
  euclid_apply (proposition_17 c a b AC AB BC)
  have hacuteB : (∠ a:b:c : ℝ) < ∟ := by euclid_finish
  have hcb : c ≠ b := by euclid_finish
  have hbd : b ≠ d := by euclid_finish
  have hce : c ≠ e := by euclid_finish
  have hde : d ≠ e := by euclid_finish
  have h_c_nBD : ¬c.onLine BD := by euclid_finish
  have h_e_nBC : ¬e.onLine BC := by euclid_finish
  have h_offCE : ¬a.onLine CE := by euclid_finish
  have hBCBD : BC ≠ BD := by euclid_finish
  have hALBD : AL ≠ BD := by euclid_finish
  have hBCCE : BC ≠ CE := by euclid_finish
  have hDEBC : DE ≠ BC := by euclid_finish
  have hBDCE : BD ≠ CE := by euclid_finish
  have s17_x1 : ¬AL.intersectsLine CE := by euclid_apply (h_1_47_s17_x1 a b c AL CE BD BC (by (show a.onLine AL; assumption)) (by (show ¬a.onLine BD; assumption)) (by (show ¬a.onLine CE; assumption)) (by (show b.onLine BD; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show c.onLine CE; assumption)) (by (show ¬c.onLine BD; assumption)) (by (show ¬AL.intersectsLine BD; assumption)) (by (show ¬BD.intersectsLine CE; assumption)))
  have hALCE : AL ≠ CE := by euclid_finish
  have s17_x9 : ¬e.sameSide a BC := by euclid_apply (h_1_47_s17_x7 a d e BC DE (by (show d.onLine DE; assumption)) (by (show e.onLine DE; assumption)) (by (show ¬DE.intersectsLine BC; assumption)) (by (show ¬d.onLine BC; assumption)) (by (show ¬e.onLine BC; assumption)) (by (show ¬a.onLine BC; assumption)) (by (show ¬d.sameSide a BC; assumption)))
  have hbc : b ≠ c := by euclid_finish
  have ham : a ≠ m := by euclid_finish
  have hb_nAL : ¬b.onLine AL := by
    intro hb_AL
    euclid_apply (intersection_lines_common_point b AL BD)
    euclid_finish
  have hc_nAL : ¬c.onLine AL := by
    intro hc_AL
    euclid_apply (intersection_lines_common_point c AL CE)
    euclid_finish
  have hbm : b ≠ m := by euclid_finish
  have hcm : c ≠ m := by euclid_finish
  have hACBC : AC ≠ BC := by euclid_finish
  have s18_x1 : formParallelogram b c d e BC DE BD CE := by euclid_apply (h_1_47_s18_x1 b c d e BC DE BD CE (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show d.onLine DE; assumption)) (by (show e.onLine DE; assumption)) (by (show b.onLine BD; assumption)) (by (show d.onLine BD; assumption)) (by (show c.onLine CE; assumption)) (by (show e.onLine CE; assumption)) (by (show ¬d.onLine BC; assumption)) (by (show ¬e.onLine BC; assumption)) (by (show DE ≠ BC; assumption)) (by (show BD ≠ CE; assumption)) (by (show ¬DE.intersectsLine BC; assumption)) (by (show ¬BD.intersectsLine CE; assumption)))
  have s17_x3 : formParallelogram m l c e AL CE BC DE := by euclid_apply (h_1_47_s17_x3 a c e l m AL CE BC DE (by (show a.onLine AL; assumption)) (by (show ¬a.onLine CE; assumption)) (by (show m.onLine AL; assumption)) (by (show l.onLine AL; assumption)) (by (show c.onLine CE; assumption)) (by (show e.onLine CE; assumption)) (by (show m.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show l.onLine DE; assumption)) (by (show e.onLine DE; assumption)) (by (show ¬e.onLine BC; assumption)) (by (show ¬AL.intersectsLine CE; assumption)) (by (show ¬DE.intersectsLine BC; assumption)))
  have s18_x4 : (∠ a:m:b : ℝ) = ∟ := by euclid_apply (h_1_47_s18_x4 a b c d m BC BD AL (by (show a.onLine AL; assumption)) (by (show m.onLine AL; assumption)) (by (show a ≠ m; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show m.onLine BC; assumption)) (by (show b ≠ c; assumption)) (by (show b ≠ m; assumption)) (by (show b.onLine BD; assumption)) (by (show d.onLine BD; assumption)) (by (show b ≠ d; assumption)) (by (show ¬a.onLine BC; assumption)) (by (show ¬d.onLine BC; assumption)) (by (show ¬a.onLine BD; assumption)) (by (show BC ≠ BD; assumption)) (by (show AL ≠ BD; assumption)) (by (show (∠ c:b:d : ℝ) = ∟; assumption)) (by (show ¬AL.intersectsLine BD; assumption)) (by (show ¬d.sameSide a BC; assumption)))
  have s18_x5 : (∠ a:m:c : ℝ) = ∟ := by euclid_apply (h_1_47_s18_x5 a b c e m BC CE AL (by (show a.onLine AL; assumption)) (by (show m.onLine AL; assumption)) (by (show a ≠ m; assumption)) (by (show c.onLine BC; assumption)) (by (show b.onLine BC; assumption)) (by (show m.onLine BC; assumption)) (by (show c ≠ b; assumption)) (by (show c ≠ m; assumption)) (by (show c.onLine CE; assumption)) (by (show e.onLine CE; assumption)) (by (show c ≠ e; assumption)) (by (show ¬a.onLine BC; assumption)) (by (show ¬e.onLine BC; assumption)) (by (show ¬a.onLine CE; assumption)) (by (show BC ≠ CE; assumption)) (by (show AL ≠ CE; assumption)) (by (show (∠ b:c:e : ℝ) = ∟; assumption)) (by (show ¬AL.intersectsLine CE; assumption)) (by (show ¬e.sameSide a BC; assumption)))
  have s18_x2 : between b m c := by euclid_apply (h_1_47_s18_x2 a b c m AB BC AC AL (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show b ≠ c; assumption)) (by (show a.onLine AC; assumption)) (by (show c.onLine AC; assumption)) (by (show ¬a.onLine BC; assumption)) (by (show AB ≠ BC; assumption)) (by (show AC ≠ BC; assumption)) (by (show a.onLine AL; assumption)) (by (show m.onLine AL; assumption)) (by (show m.onLine BC; assumption)) (by (show (∠ a:b:c : ℝ) < ∟; assumption)) (by (show (∠ a:c:b : ℝ) < ∟; assumption)) (by (show (∠ a:m:b : ℝ) = ∟; assumption)) (by (show (∠ a:m:c : ℝ) = ∟; assumption)))
  have s18_x3 : between d l e := by euclid_apply (h_1_47_s18_x3 a b c d e l m BC BD CE DE AL (by (show a.onLine AL; assumption)) (by (show ¬a.onLine BD; assumption)) (by (show ¬a.onLine CE; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show b.onLine BD; assumption)) (by (show c.onLine CE; assumption)) (by (show d.onLine BD; assumption)) (by (show e.onLine CE; assumption)) (by (show d.onLine DE; assumption)) (by (show e.onLine DE; assumption)) (by (show d ≠ e; assumption)) (by (show l.onLine AL; assumption)) (by (show l.onLine DE; assumption)) (by (show m.onLine AL; assumption)) (by (show m.onLine BC; assumption)) (by (show between b m c; assumption)) (by (show ¬AL.intersectsLine BD; assumption)) (by (show ¬AL.intersectsLine CE; assumption)))
  euclid_apply (sum_parallelograms_area b c d e m l BC DE BD CE)
  euclid_apply (parallelogram_area m l c e AL CE BC DE)
  euclid_finish

end Elements.Book1

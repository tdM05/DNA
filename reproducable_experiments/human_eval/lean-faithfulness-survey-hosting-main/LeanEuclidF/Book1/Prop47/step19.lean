import SystemE
import Book1.Prop47.step18_bdec
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_47_s19
    (b c d e : Point) (BC DE BD CE : Line)
    (hb_BC : b.onLine BC) (hc_BC : c.onLine BC)
    (hd_DE : d.onLine DE) (he_DE : e.onLine DE)
    (hb_BD : b.onLine BD) (hd_BD : d.onLine BD)
    (hc_CE : c.onLine CE) (he_CE : e.onLine CE)
    (h_d_nBC : ¬d.onLine BC)
    (h_cbd : (∠ c:b:d : ℝ) = ∟) (h_bde : (∠ b:d:e : ℝ) = ∟)
    (hbd_len : |(b─d)| = |(b─c)|)
    (h_nDEBC : ¬DE.intersectsLine BC) (h_nBDCE : ¬BD.intersectsLine CE) :
    Triangle.area △ b:d:e + Triangle.area △ b:e:c = |(b─c)| * |(b─c)| := by
  have hDEBC : DE ≠ BC := by euclid_finish
  have h_e_nBC : ¬e.onLine BC := by
    intro he_BC
    euclid_apply (intersection_lines_common_point e DE BC)
    euclid_finish
  have hcb : c ≠ b := by euclid_finish
  have hBDCE : BD ≠ CE := by euclid_finish
  have s18_x1 : formParallelogram b c d e BC DE BD CE := by euclid_apply (h_1_47_s18_x1 b c d e BC DE BD CE (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show d.onLine DE; assumption)) (by (show e.onLine DE; assumption)) (by (show b.onLine BD; assumption)) (by (show d.onLine BD; assumption)) (by (show c.onLine CE; assumption)) (by (show e.onLine CE; assumption)) (by (show ¬d.onLine BC; assumption)) (by (show ¬e.onLine BC; assumption)) (by (show DE ≠ BC; assumption)) (by (show BD ≠ CE; assumption)) (by (show ¬DE.intersectsLine BC; assumption)) (by (show ¬BD.intersectsLine CE; assumption)))
  euclid_apply (rectangle_area b c d e BC DE BD CE)
  euclid_finish

end Elements.Book1

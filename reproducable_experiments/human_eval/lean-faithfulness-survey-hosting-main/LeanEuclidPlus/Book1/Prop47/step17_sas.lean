import SystemE
import Book1.Prop04.Main
import Book1.Prop47.step17_sas_tri1
import Book1.Prop47.step17_sas_tri2
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_47_s17_x9
    (a b c e k : Point) (CE AE AC BC BK CK : Line)
    (hc_CE : c.onLine CE) (he_CE : e.onLine CE)
    (ha_AE : a.onLine AE) (he_AE : e.onLine AE)
    (ha_AC : a.onLine AC) (hc_AC : c.onLine AC)
    (hb_BC : b.onLine BC) (hc_BC : c.onLine BC)
    (hb_BK : b.onLine BK) (hk_BK : k.onLine BK)
    (hc_CK : c.onLine CK) (hk_CK : k.onLine CK)
    (hce_len : |(c─e)| = |(b─c)|) (hck_len : |(c─k)| = |(a─c)|)
    (h_eca_bck : ∠ e:c:a = ∠ b:c:k)
    (h_a_nCE : ¬a.onLine CE) (h_k_nBC : ¬k.onLine BC)
    (hcb : c ≠ b) (hca : c ≠ a) :
    Triangle.area △ a:c:e = Triangle.area △ c:b:k := by
  have s17_x13 : formTriangle c e a CE AE AC := by euclid_apply (h_1_47_s17_x11 a b c e CE AE AC (by (show c.onLine CE; assumption)) (by (show e.onLine CE; assumption)) (by (show a.onLine AE; assumption)) (by (show e.onLine AE; assumption)) (by (show a.onLine AC; assumption)) (by (show c.onLine AC; assumption)) (by (show |(c─e)| = |(b─c)|; assumption)) (by (show ¬a.onLine CE; assumption)) (by (show c ≠ b; assumption)) (by (show c ≠ a; assumption)))
  have s17_x14 : formTriangle c b k BC BK CK := by euclid_apply (h_1_47_s17_x12 a b c k BC BK CK (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show b.onLine BK; assumption)) (by (show k.onLine BK; assumption)) (by (show c.onLine CK; assumption)) (by (show k.onLine CK; assumption)) (by (show |(c─k)| = |(a─c)|; assumption)) (by (show ¬k.onLine BC; assumption)) (by (show c ≠ b; assumption)) (by (show c ≠ a; assumption)))
  euclid_apply (proposition_4 c e a c b k CE AE AC BC BK CK)
  euclid_finish

end Elements.Book1

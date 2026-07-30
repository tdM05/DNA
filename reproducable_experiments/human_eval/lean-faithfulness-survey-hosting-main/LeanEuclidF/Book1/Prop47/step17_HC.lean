import SystemE
import Book1.Prop41.Main
import Book1.Prop47.step17_HC_pgram
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_47_s17_x4
    (a b c h k : Point) (AC AH CK HK BK BC : Line)
    (hh_AH : h.onLine AH) (ha_AH : a.onLine AH)
    (hk_CK : k.onLine CK) (hc_CK : c.onLine CK)
    (hh_HK : h.onLine HK) (hk_HK : k.onLine HK)
    (ha_AC : a.onLine AC) (hc_AC : c.onLine AC) (hac : a ≠ c)
    (hb_BK : b.onLine BK) (hk_BK : k.onLine BK)
    (hb_BC : b.onLine BC) (hc_BC : c.onLine BC)
    (hh_nAC : ¬h.onLine AC)
    (h_nAHCK : ¬AH.intersectsLine CK) (h_nHKAC : ¬HK.intersectsLine AC)
    (h_bah : between b a h) :
    Triangle.area △ a:h:k + Triangle.area △ a:k:c = Triangle.area △ c:b:k + Triangle.area △ c:b:k := by
  have s17_x5 : formParallelogram h a k c AH CK HK AC := by euclid_apply (h_1_47_s17_x5 a c h k AH CK HK AC (by (show h.onLine AH; assumption)) (by (show a.onLine AH; assumption)) (by (show k.onLine CK; assumption)) (by (show c.onLine CK; assumption)) (by (show h.onLine HK; assumption)) (by (show k.onLine HK; assumption)) (by (show a.onLine AC; assumption)) (by (show c.onLine AC; assumption)) (by (show a ≠ c; assumption)) (by (show ¬h.onLine AC; assumption)) (by (show ¬AH.intersectsLine CK; assumption)) (by (show ¬HK.intersectsLine AC; assumption)))
  euclid_apply (proposition_41 h k c a b AH CK HK AC BK BC)
  euclid_apply (parallelogram_area h a k c AH CK HK AC)
  euclid_finish

end Elements.Book1

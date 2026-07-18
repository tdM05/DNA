import SystemE
import Book1.Prop41.Main
import Book1.Prop47.step17_koffBC
import Book1.Prop47.step17_hc_par
import Book1.Prop47.step17_hc_tri
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_47_step17_hc
    (a b c h k : Point) (AB BC AC CK HK BK : Line)
    (hcAC : c.onLine AC) (haAC : a.onLine AC)
    (hkCK : k.onLine CK) (hcCK : c.onLine CK)
    (hhHK : h.onLine HK) (hkHK : k.onLine HK)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hbBK : b.onLine BK) (hkBK : k.onLine BK)
    (hcBC : c.onLine BC) (hbBC : b.onLine BC)
    (hbah : between b a h) (hhoffAC : ¬h.onLine AC)
    (hACCK : ¬CK.intersectsLine AB) (hHKAC : ¬HK.intersectsLine AC)
    (hbac : ∠ b:a:c = ∟) (hack : ∠ a:c:k = ∟) (haoffBC : ¬a.onLine BC)
    (hACBC : AC ≠ BC) (hBCAB : BC ≠ AB) (hABAC : AB ≠ AC)
    (hac : a ≠ c) (hkc : k ≠ c) (hbc : b ≠ c) :
    Triangle.area △ a:h:k + Triangle.area △ a:k:c =
      Triangle.area △ k:c:b + Triangle.area △ k:c:b := by
  have hcb : c ≠ b := Ne.symm hbc
  have hABCK : ¬AB.intersectsLine CK := by euclid_finish
  have step17_koffBC : ¬k.onLine BC := by euclid_apply (helper_1_47_step17_koffBC a b c k AC BC AB (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show AC ≠ BC; assumption)) (by euclid_assumption "" (show BC ≠ AB; assumption)) (by euclid_assumption "" (show AB ≠ AC; assumption)) (by euclid_assumption "" (show ∠ b:a:c = ∟; assumption)) (by euclid_assumption "" (show ∠ a:c:k = ∟; assumption)) (by euclid_assumption "" (show ¬a.onLine BC; assumption)) (by euclid_assumption "" (show k ≠ c; assumption)) (by euclid_assumption "" (show b ≠ c; assumption)))
  have hCKBC : CK ≠ BC := fun h => step17_koffBC (h ▸ hkCK)
  have hboffCK : ¬b.onLine CK := by euclid_finish
  have hkb : k ≠ b := by euclid_finish
  have step17_hc_par : formParallelogram h a k c AB CK HK AC := by euclid_apply (helper_1_47_step17_hc_par a b c h k AB CK HK AC (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show k.onLine CK; assumption)) (by euclid_assumption "" (show c.onLine CK; assumption)) (by euclid_assumption "" (show h.onLine HK; assumption)) (by euclid_assumption "" (show k.onLine HK; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show between b a h; assumption)) (by euclid_assumption "" (show ¬h.onLine AC; assumption)) (by euclid_assumption "" (show ¬AB.intersectsLine CK; assumption)) (by euclid_assumption "" (show ¬HK.intersectsLine AC; assumption)) (by euclid_assumption "" (show a ≠ c; assumption)))
  have step17_hc_tri : formTriangle b k c BK CK BC := by euclid_apply (helper_1_47_step17_hc_tri b c k BK CK BC AB (by euclid_assumption "" (show b.onLine BK; assumption)) (by euclid_assumption "" (show k.onLine BK; assumption)) (by euclid_assumption "" (show k.onLine CK; assumption)) (by euclid_assumption "" (show c.onLine CK; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show ¬k.onLine BC; assumption)) (by euclid_assumption "" (show ¬b.onLine CK; assumption)) (by euclid_assumption "" (show k ≠ b; assumption)) (by euclid_assumption "" (show c ≠ b; assumption)))
  euclid_apply (proposition_41 h k c a b AB CK HK AC BK BC)
  euclid_apply (parallelogram_area h a k c AB CK HK AC)
  euclid_finish

end Elements.Book1

import SystemE
import Book1.Prop04.Main
import Book1.Prop47.step17_koffBC
import Book1.Prop47.step17_area_T1
import Book1.Prop47.step17_area_T2
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_47_step17_area
    (a b c e k : Point) (AC BC CE AE CK BK AB : Line)
    (hcCE : c.onLine CE) (heCE : e.onLine CE)
    (heAE : e.onLine AE) (haAE : a.onLine AE)
    (haAC : a.onLine AC) (hcAC : c.onLine AC)
    (hcBC : c.onLine BC) (hbBC : b.onLine BC)
    (hbBK : b.onLine BK) (hkBK : k.onLine BK)
    (hkCK : k.onLine CK) (hcCK : c.onLine CK)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (haoffCE : ¬a.onLine CE) (haoffBC : ¬a.onLine BC)
    (hbac : ∠ b:a:c = ∟) (hack : ∠ a:c:k = ∟)
    (hACBC : AC ≠ BC) (hBCAB : BC ≠ AB) (hABAC : AB ≠ AC)
    (hac : a ≠ c) (hkc : k ≠ c) (hbc : b ≠ c)
    (hcelen : |(c─e)| = |(b─c)|) (hcklen : |(c─k)| = |(a─c)|)
    (hstep17_ang : ∠ e:c:a = ∠ k:c:b) :
    Triangle.area △ a:c:e = Triangle.area △ k:c:b := by
  have hcb : c ≠ b := Ne.symm hbc
  have hce : c ≠ e := by euclid_finish
  have heoffAC : ¬e.onLine AC := by euclid_finish
  have hae : a ≠ e := by euclid_finish
  have hkb : k ≠ b := by euclid_finish
  have step17_koffBC : ¬k.onLine BC := by euclid_apply (helper_1_47_step17_koffBC a b c k AC BC AB (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show AC ≠ BC; assumption)) (by euclid_assumption "" (show BC ≠ AB; assumption)) (by euclid_assumption "" (show AB ≠ AC; assumption)) (by euclid_assumption "" (show ∠ b:a:c = ∟; assumption)) (by euclid_assumption "" (show ∠ a:c:k = ∟; assumption)) (by euclid_assumption "" (show ¬a.onLine BC; assumption)) (by euclid_assumption "" (show k ≠ c; assumption)) (by euclid_assumption "" (show b ≠ c; assumption)))
  have hCKBC : CK ≠ BC := fun h => step17_koffBC (h ▸ hkCK)
  have hboffCK : ¬b.onLine CK := by euclid_finish
  have step17_area_T1 : formTriangle c e a CE AE AC := by euclid_apply (helper_1_47_step17_area_T1 a c e CE AE AC (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e.onLine CE; assumption)) (by euclid_assumption "" (show e.onLine AE; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show ¬a.onLine CE; assumption)) (by euclid_assumption "" (show ¬e.onLine AC; assumption)) (by euclid_assumption "" (show a ≠ c; assumption)) (by euclid_assumption "" (show a ≠ e; assumption)))
  have step17_area_T2 : formTriangle c b k BC BK CK := by euclid_apply (helper_1_47_step17_area_T2 b c k BC BK CK (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show b.onLine BK; assumption)) (by euclid_assumption "" (show k.onLine BK; assumption)) (by euclid_assumption "" (show k.onLine CK; assumption)) (by euclid_assumption "" (show c.onLine CK; assumption)) (by euclid_assumption "" (show ¬k.onLine BC; assumption)) (by euclid_assumption "" (show ¬b.onLine CK; assumption)) (by euclid_assumption "" (show k ≠ b; assumption)) (by euclid_assumption "" (show c ≠ b; assumption)))
  euclid_apply (proposition_4 c e a c b k CE AE AC BC BK CK)
  euclid_apply (area_congruence a c e k c b)
  euclid_finish

end Elements.Book1

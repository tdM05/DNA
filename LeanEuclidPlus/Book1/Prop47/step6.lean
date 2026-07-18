import SystemE
import Book1.Prop14.Main
import Book1.Prop47.step6_opp
import Book1.Prop47.step6_sum
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_47_step6
    (a b c h : Point) (AB AC AH BC : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hab : a ≠ b)
    (hcAC : c.onLine AC) (haAC : a.onLine AC)
    (hhAH : h.onLine AH) (haAH : a.onLine AH)
    (hcBC : c.onLine BC) (haoffBC : ¬a.onLine BC)
    (hACAB : AC ≠ AB)
    (hbac : ∠ b:a:c = ∟) (hcah : ∠ c:a:h = ∟)
    (hhb : ¬h.sameSide b AC) (hboffAC : ¬b.onLine AC) (hhoffAC : ¬h.onLine AC) :
    between b a h := by
  have step6_opp : b.opposingSides h AC := by euclid_apply (helper_1_47_step6_opp b h AC (by euclid_assumption "" (show ¬h.sameSide b AC; assumption)) (by euclid_assumption "" (show ¬b.onLine AC; assumption)) (by euclid_assumption "" (show ¬h.onLine AC; assumption)))
  have step6_sum : ∠ c:a:b + ∠ c:a:h = ∟ + ∟ := by euclid_apply (helper_1_47_step6_sum a b c h BC (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show ¬a.onLine BC; assumption)) (by euclid_assumption "" (show ∠ b:a:c = ∟; assumption)) (by euclid_assumption "" (show ∠ c:a:h = ∟; assumption)))
  euclid_apply (proposition_14 c a b h AC AB AH)
  euclid_apply (pasch_4 b a h AC AB)
  euclid_finish

end Elements.Book1

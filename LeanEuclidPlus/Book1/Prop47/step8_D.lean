import SystemE
import Book1.Prop17.Main
import Book1.Prop47.step8_D_pab
import Book1.Prop47.step8_D_abp
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

-- c.sameSide a BF: if BF separated a and c, the crossing point p = AC ∩ BF would make triangle
-- p a b have right angles at both a (∠pab = ∠cab = ∟, p on AC) and b (∠abp = ∠abf = ∟, p on BF),
-- impossible by Prop.1.17.
theorem helper_1_47_step8_D
    (a b c f : Point) (AB BC BF AC : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hcAC : c.onLine AC) (haAC : a.onLine AC)
    (hbBF : b.onLine BF) (hfBF : f.onLine BF)
    (hbac : ∠ b:a:c = ∟) (habf : ∠ a:b:f = ∟)
    (haoffBF : ¬a.onLine BF) (hcoffBF : ¬c.onLine BF)
    (hACAB : AC ≠ AB) (hBFAB : BF ≠ AB) (hACBF : AC ≠ BF)
    (hab : a ≠ b) (hac : a ≠ c) (hfb : f ≠ b) :
    c.sameSide a BF := by
  by_contra hns
  have hint : AC.intersectsLine BF := by
    euclid_apply (intersection_lines_opposing a c BF AC)
    euclid_finish
  euclid_apply (intersection_lines AC BF) as p
  have hbetween : between a p c := by euclid_finish
  have hpa : p ≠ a := by euclid_finish
  have hpb : p ≠ b := by euclid_finish
  have hca : c ≠ a := Ne.symm hac
  have hba : b ≠ a := Ne.symm hab
  have step8_D_pab : ∠ p:a:b = ∟ := by euclid_apply (helper_1_47_step8_D_pab a b c p AC AB (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show p.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show ∠ b:a:c = ∟; assumption)) (by euclid_assumption "" (show between a p c; assumption)) (by euclid_assumption "" (show p ≠ a; assumption)) (by euclid_assumption "" (show c ≠ a; assumption)) (by euclid_assumption "" (show b ≠ a; assumption)))
  have step8_D_abp : ∠ a:b:p = ∟ := by euclid_apply (helper_1_47_step8_D_abp a b f p BF AB (by euclid_assumption "" (show b.onLine BF; assumption)) (by euclid_assumption "" (show f.onLine BF; assumption)) (by euclid_assumption "" (show p.onLine BF; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show ∠ a:b:f = ∟; assumption)) (by euclid_assumption "" (show p ≠ b; assumption)) (by euclid_assumption "" (show f ≠ b; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)))
  euclid_apply (proposition_17 p a b AC AB BF)
  euclid_finish

end Elements.Book1

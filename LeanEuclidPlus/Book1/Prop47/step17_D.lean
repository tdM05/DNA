import SystemE
import Book1.Prop17.Main
import Book1.Prop47.step17_D_pac
import Book1.Prop47.step17_D_acp
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

-- b.sameSide a CK: if CK separated a and b, crossing p = AB ∩ CK makes triangle p a c have right
-- angles at a (∠pac = ∠bac = ∟, p on AB) and c (∠acp = ∠ack = ∟, p on CK). Prop.1.17 ⟹ contra.
theorem helper_1_47_step17_D
    (a b c k : Point) (AB BC CK AC : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hcAC : c.onLine AC) (haAC : a.onLine AC)
    (hcCK : c.onLine CK) (hkCK : k.onLine CK)
    (hcab : ∠ c:a:b = ∟) (hack : ∠ a:c:k = ∟)
    (haoffCK : ¬a.onLine CK) (hboffCK : ¬b.onLine CK)
    (hABAC : AB ≠ AC) (hCKAC : CK ≠ AC) (hABCK : AB ≠ CK)
    (hac : a ≠ c) (hab : a ≠ b) (hkc : k ≠ c) :
    b.sameSide a CK := by
  by_contra hns
  have hint : AB.intersectsLine CK := by
    euclid_apply (intersection_lines_opposing a b CK AB)
    euclid_finish
  euclid_apply (intersection_lines AB CK) as p
  have hbetween : between a p b := by euclid_finish
  have hpa : p ≠ a := by euclid_finish
  have hpc : p ≠ c := by euclid_finish
  have hba : b ≠ a := Ne.symm hab
  have hca : c ≠ a := Ne.symm hac
  have step17_D_pac : ∠ p:a:c = ∟ := by euclid_apply (helper_1_47_step17_D_pac a b c p AB AC (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show p.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show ∠ c:a:b = ∟; assumption)) (by euclid_assumption "" (show between a p b; assumption)) (by euclid_assumption "" (show p ≠ a; assumption)) (by euclid_assumption "" (show b ≠ a; assumption)) (by euclid_assumption "" (show c ≠ a; assumption)))
  have step17_D_acp : ∠ a:c:p = ∟ := by euclid_apply (helper_1_47_step17_D_acp a c k p CK AC (by euclid_assumption "" (show c.onLine CK; assumption)) (by euclid_assumption "" (show k.onLine CK; assumption)) (by euclid_assumption "" (show p.onLine CK; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show ∠ a:c:k = ∟; assumption)) (by euclid_assumption "" (show p ≠ c; assumption)) (by euclid_assumption "" (show k ≠ c; assumption)) (by euclid_assumption "" (show a ≠ c; assumption)))
  euclid_apply (proposition_17 p a c AB AC CK)
  euclid_finish

end Elements.Book1

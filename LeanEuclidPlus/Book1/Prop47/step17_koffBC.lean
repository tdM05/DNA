import SystemE
import Book1.Prop17.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

-- k off BC: else ∠ack (=∟) forces ∠acb = ∟, giving triangle abc two right angles (at a and c).
theorem helper_1_47_step17_koffBC
    (a b c k : Point) (AC BC AB : Line)
    (hcAC : c.onLine AC) (haAC : a.onLine AC)
    (hbBC : b.onLine BC) (hcBC : c.onLine BC)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hACBC : AC ≠ BC) (hBCAB : BC ≠ AB) (hABAC : AB ≠ AC)
    (hbac : ∠ b:a:c = ∟) (hack : ∠ a:c:k = ∟)
    (haoffBC : ¬a.onLine BC) (hkc : k ≠ c) (hbc : b ≠ c) :
    ¬k.onLine BC := by
  intro hkBC
  have hacb : ∠ a:c:b = ∟ := by
    by_cases h : between k c b
    · euclid_finish
    · euclid_apply (equal_angles c k b a a BC AC)
      euclid_finish
  euclid_apply (proposition_17 b a c AB AC BC)
  euclid_finish

end Elements.Book1

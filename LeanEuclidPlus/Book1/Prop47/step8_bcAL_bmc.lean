import SystemE
import Book1.Prop13.Main
import Book1.Prop17.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

-- foot m between b,c: if not, one base angle would be ≥ right-angle, contradicting the acute
-- base angles of the right triangle (angle sum with the right angle at a).
theorem helper_1_47_step8_bcAL_bmc
    (a b c m : Point) (AB BC AC AL : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hbBC : b.onLine BC) (hcBC : c.onLine BC) (hmBC : m.onLine BC)
    (hcAC : c.onLine AC) (haAC : a.onLine AC)
    (haAL : a.onLine AL) (hmAL : m.onLine AL)
    (hABBC : AB ≠ BC) (hBCAC : BC ≠ AC) (hACAB : AC ≠ AB)
    (hABAL : AB ≠ AL) (hACAL : AC ≠ AL) (hBCAL : BC ≠ AL)
    (haoffBC : ¬a.onLine BC) (hmb : m ≠ b) (hmc : m ≠ c) (hbc : b ≠ c)
    (hab : a ≠ b) (hac : a ≠ c) (ham : a ≠ m)
    (hbac : ∠ b:a:c = ∟) (hperp : ∠ a:m:b = ∟)
    (hsum : ∠ a:b:c + ∠ b:c:a + ∠ c:a:b = ∟ + ∟) :
    between b m c := by
  euclid_apply (angle_symm b a c)
  rcases between_points b m c BC ⟨hmb.symm, hmc, hbc.symm, hbBC, hmBC, hcBC⟩ with h | h | h
  · exact h
  · exfalso
    -- b between m and c: ∠c:b:a + ∠a:b:m = 2∟, and triangle abm has ∠a:m:b = ∟ ⟹ ∠a:b:m < ∟
    euclid_apply (proposition_13 a b c m AB BC)
    euclid_apply (proposition_17 a b m AB BC AL)
    euclid_finish
  · exfalso
    euclid_apply (proposition_13 a c b m AC BC)
    euclid_apply (proposition_17 a c m AC BC AL)
    euclid_finish

end Elements.Book1

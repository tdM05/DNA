import SystemE
import Book1.Prop17.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

-- f is off BC: else ∠abf (=∟) would force the base angle ∠abc = ∟, giving triangle abc two
-- right angles (at a and b), impossible by Prop.1.17.
theorem helper_1_47_step11_foffBC
    (a b c f : Point) (AB BC AC BF : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hbBC : b.onLine BC) (hcBC : c.onLine BC)
    (hcAC : c.onLine AC) (haAC : a.onLine AC)
    (hbBF : b.onLine BF) (hfBF : f.onLine BF)
    (hABBC : AB ≠ BC) (hBCAC : BC ≠ AC) (hACAB : AC ≠ AB)
    (hbac : ∠ b:a:c = ∟) (habf : ∠ a:b:f = ∟)
    (haoffBC : ¬a.onLine BC) (hfb : f ≠ b) (hcb : c ≠ b) (hab : a ≠ b) :
    ¬f.onLine BC := by
  intro hfBC
  have habc : ∠ a:b:c = ∟ := by
    by_cases h : between f b c
    · euclid_finish
    · euclid_apply (equal_angles b f c a a BC AB)
      euclid_finish
  euclid_apply (proposition_17 c a b AC AB BC)
  euclid_finish

end Elements.Book1

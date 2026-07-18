import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_47_step17_D_pac
    (a b c p : Point) (AB AC : Line)
    (hbAB : b.onLine AB) (haAB : a.onLine AB) (hpAB : p.onLine AB)
    (haAC : a.onLine AC) (hcAC : c.onLine AC)
    (hcab : ∠ c:a:b = ∟) (hbetween : between a p b)
    (hpa : p ≠ a) (hba : b ≠ a) (hca : c ≠ a) :
    ∠ p:a:c = ∟ := by
  euclid_apply (equal_angles a p b c c AB AC)
  euclid_finish

end Elements.Book1

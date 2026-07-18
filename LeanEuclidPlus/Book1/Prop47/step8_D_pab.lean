import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_47_step8_D_pab
    (a b c p : Point) (AC AB : Line)
    (hcAC : c.onLine AC) (haAC : a.onLine AC) (hpAC : p.onLine AC)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hbac : ∠ b:a:c = ∟) (hbetween : between a p c)
    (hpa : p ≠ a) (hca : c ≠ a) (hba : b ≠ a) :
    ∠ p:a:b = ∟ := by
  euclid_apply (equal_angles a p c b b AC AB)
  euclid_finish

end Elements.Book1

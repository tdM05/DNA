import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_6_s6 (a b c d : Point) (AB BC AC : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hab : a ≠ b)
    (hbBC : b.onLine BC) (hcBC : c.onLine BC)
    (hcAC : c.onLine AC) (haAC : a.onLine AC)
    (hABneBC : AB ≠ BC) (hBCneAC : BC ≠ AC) (hACneAB : AC ≠ AB)
    (hbda : between b d a) (habc_acb : ∠ a:b:c = ∠ a:c:b) :
    ∠ d:b:c = ∠ a:c:b := by
  have hdb_abc : ∠ d:b:c = ∠ a:b:c := by
    euclid_apply (equal_angles b d a c c AB BC)
    assumption
  exact hdb_abc.trans habc_acb

end Elements.Book1

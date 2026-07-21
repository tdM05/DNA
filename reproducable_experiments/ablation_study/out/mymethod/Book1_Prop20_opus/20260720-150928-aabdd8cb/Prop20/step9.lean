import SystemE
import Book1.Prop20.step9_triineq
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_20_step9 (a b c : Point) (AB BC AC : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hab : a ≠ b)
    (hbBC : b.onLine BC) (hcBC : c.onLine BC)
    (hcAC : c.onLine AC) (haAC : a.onLine AC)
    (hABBC : AB ≠ BC) (hBCAC : BC ≠ AC) (hACAB : AC ≠ AB)
    : |(a─b)| + |(b─c)| > |(a─c)| := by
  have htri9 : formTriangle b a c AB AC BC := by euclid_finish
  -- @args: b a c AB AC BC
  have step9_triineq : |(a─b)| + |(b─c)| > |(a─c)| := by euclid_apply (helper_1_20_step9_triineq b a c AB AC BC (by euclid_assumption "" (show formTriangle b a c AB AC BC; assumption)))
  exact step9_triineq

end Elements.Book1

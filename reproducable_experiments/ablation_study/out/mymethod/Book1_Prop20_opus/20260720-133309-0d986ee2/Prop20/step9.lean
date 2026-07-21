import SystemE
import Book1.Prop20.step9_triineq
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_20_step9 (a b c : Point) (AB BC AC : Line)
    (h_aAB : a.onLine AB) (h_bAB : b.onLine AB) (h_ab : a ≠ b)
    (h_bBC : b.onLine BC) (h_cBC : c.onLine BC) (h_cAC : c.onLine AC) (h_aAC : a.onLine AC)
    (h_ABBC : AB ≠ BC) (h_BCAC : BC ≠ AC) (h_ACAB : AC ≠ AB)
    : |(a─b)| + |(b─c)| > |(a─c)| := by
  have htri9 : formTriangle b a c AB AC BC := by euclid_finish
  -- @args: b a c AB AC BC
  have step9_triineq : |(b─a)| + |(b─c)| > |(a─c)| := by euclid_apply (helper_1_20_step9_triineq b a c AB AC BC (by euclid_assumption "" (show formTriangle b a c AB AC BC; assumption)))
  euclid_finish

end Elements.Book1

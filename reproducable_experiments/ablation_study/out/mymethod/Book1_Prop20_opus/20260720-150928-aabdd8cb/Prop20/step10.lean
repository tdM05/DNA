import SystemE
import Book1.Prop20.step9_triineq
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_20_step10 (a b c : Point) (AB BC AC : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hab : a ≠ b)
    (hbBC : b.onLine BC) (hcBC : c.onLine BC)
    (hcAC : c.onLine AC) (haAC : a.onLine AC)
    (hABBC : AB ≠ BC) (hBCAC : BC ≠ AC) (hACAB : AC ≠ AB)
    : |(b─c)| + |(c─a)| > |(a─b)| := by
  have htri10 : formTriangle c b a BC AB AC := by euclid_finish
  -- @args: c b a BC AB AC
  have step9_triineq : |(b─c)| + |(c─a)| > |(b─a)| := by euclid_apply (helper_1_20_step9_triineq c b a BC AB AC (by euclid_assumption "" (show formTriangle c b a BC AB AC; assumption)))
  euclid_finish

end Elements.Book1

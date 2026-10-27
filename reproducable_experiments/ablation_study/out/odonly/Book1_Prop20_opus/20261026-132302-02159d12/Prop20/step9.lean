import SystemE
import Book1.Prop20.step9_tri
import Book1.Prop20.step9_ineq
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_20_step9 (a b c : Point) (AB BC AC : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hab : a ≠ b)
    (hbBC : b.onLine BC) (hcBC : c.onLine BC)
    (hcAC : c.onLine AC) (haAC : a.onLine AC)
    (hABBC : AB ≠ BC) (hBCAC : BC ≠ AC) (hACAB : AC ≠ AB) :
    |(a─b)| + |(b─c)| > |(a─c)| := by
  have step9_tri : formTriangle b a c AB AC BC := by euclid_apply (helper_1_20_step9_tri a b c AB BC AC (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show AB ≠ BC; assumption)) (by euclid_assumption "" (show BC ≠ AC; assumption)) (by euclid_assumption "" (show AC ≠ AB; assumption)))
  -- @args: b a c AB AC BC
  have step9_ineq : |(a─b)| + |(b─c)| > |(a─c)| := by euclid_apply (helper_1_20_step9_ineq b a c AB AC BC (by euclid_assumption "" (show formTriangle b a c AB AC BC; assumption)))
  exact step9_ineq

end Elements.Book1

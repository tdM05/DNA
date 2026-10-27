import SystemE
import Book1.Prop20.step9_triineq
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_20_step9
    (a b c : Point)
    (AB BC AC : Line)
    (ha_AB : a.onLine AB)
    (hb_AB : b.onLine AB)
    (hab : a ≠ b)
    (hb_BC : b.onLine BC)
    (hc_BC : c.onLine BC)
    (hc_AC : c.onLine AC)
    (ha_AC : a.onLine AC)
    (hABBC : AB ≠ BC)
    (hBCAC : BC ≠ AC)
    (hACAB : AC ≠ AB)
    : |(a─b)| + |(b─c)| > |(a─c)| := by
  -- @args: a b c AB BC AC
  have step9_triineq : |(a─b)| + |(b─c)| > |(a─c)| := by euclid_apply (helper_1_20_step9_triineq a b c AB BC AC (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show AB ≠ BC; assumption)) (by euclid_assumption "" (show BC ≠ AC; assumption)) (by euclid_assumption "" (show AC ≠ AB; assumption)))
  euclid_finish

end Elements.Book1

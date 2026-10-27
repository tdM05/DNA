import SystemE
import Book1.Prop20.step9_ti
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_20_step10 (a b c : Point) (AB BC AC : Line)
  (h_aAB : a.onLine AB) (h_bAB : b.onLine AB) (h_ab_ne : a ≠ b)
  (h_bBC : b.onLine BC) (h_cBC : c.onLine BC)
  (h_cAC : c.onLine AC) (h_aAC : a.onLine AC)
  (h_AB_ne_BC : AB ≠ BC) (h_BC_ne_AC : BC ≠ AC) (h_AC_ne_AB : AC ≠ AB)
  : |(b─c)| + |(c─a)| > |(a─b)| := by
  have hft : formTriangle c b a BC AB AC := by euclid_finish
  -- @args: c b a BC AB AC
  have step9_ti : |(b─c)| + |(c─a)| > |(b─a)| := by euclid_apply (helper_1_20_step9_ti c b a BC AB AC (by euclid_assumption "" (show formTriangle c b a BC AB AC; assumption)))
  euclid_finish

end Elements.Book1

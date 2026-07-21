import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_20_step5 (a b c d d' : Point) (AB BC AC DC : Line)
    (haAB : a.onLine AB) (hd'AB : d'.onLine AB) (hadd' : between a d d')
    (hbBC : b.onLine BC) (hcBC : c.onLine BC)
    (hcAC : c.onLine AC) (haAC : a.onLine AC)
    (hABBC : AB ≠ BC) (hBCAC : BC ≠ AC) (hACAB : AC ≠ AB)
    (hdDC : d.onLine DC) (hcDC : c.onLine DC)
    (hbad : between b a d)
    (hstep4 : ∠ a:d:c = ∠ a:c:d)
    : ∠ b:c:d > ∠ a:d:c := by
  have haDC : ¬ a.onLine DC := by euclid_finish
  have haBC : ¬ a.onLine BC := by euclid_finish
  euclid_apply (pasch_2 d a b DC)
  euclid_apply (pasch_2 b a d BC)
  euclid_finish

end Elements.Book1

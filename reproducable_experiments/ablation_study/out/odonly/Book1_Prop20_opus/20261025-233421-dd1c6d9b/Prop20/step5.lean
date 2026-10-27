import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_20_step5
    (a b c d d' : Point)
    (AB BC AC DC : Line)
    (ha_AB : a.onLine AB)
    (hb_AB : b.onLine AB)
    (hab : a ≠ b)
    (hbBC : b.onLine BC)
    (hcBC : c.onLine BC)
    (hcAC : c.onLine AC)
    (haAC : a.onLine AC)
    (hABBC : AB ≠ BC)
    (hBCAC : BC ≠ AC)
    (hACAB : AC ≠ AB)
    (hd'_AB : d'.onLine AB)
    (hadd' : between a d d')
    (hdDC : d.onLine DC)
    (hcDC : c.onLine DC)
    (step1 : between b a d)
    (step4 : ∠ a:d:c = ∠ a:c:d)
    : ∠ b:c:d > ∠ a:d:c := by
  euclid_apply (sum_angles_onlyif c b d a BC DC)
  euclid_finish

end Elements.Book1

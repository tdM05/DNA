import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_20_step9_ang (a b c d : Point) (AB BC AC DC : Line)
    (h4 : ∠ a:d:c = ∠ a:c:d) (hbad : between b a d)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hcBC : c.onLine BC) (hbBC : b.onLine BC)
    (hcAC : c.onLine AC) (haAC : a.onLine AC)
    (hdDC : d.onLine DC) (hcDC : c.onLine DC)
    (hABBC : AB ≠ BC) (hACAB : AC ≠ AB) :
    ∠ b:c:d > ∠ a:d:c := by
  euclid_apply (sum_angles_onlyif c b d a BC DC)
  euclid_finish

end Elements.Book1

import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_20_step9_tri2 (a b c d : Point) (AB BC DC AC : Line)
    (hbad : between b a d) (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hbBC : b.onLine BC) (hcBC : c.onLine BC)
    (hcDC : c.onLine DC) (hdDC : d.onLine DC)
    (hcAC : c.onLine AC) (haAC : a.onLine AC)
    (hABBC : AB ≠ BC) (hACAB : AC ≠ AB) : formTriangle b c d BC DC AB := by
  have hdAB : d.onLine AB := by euclid_finish
  have hcoff : ¬ c.onLine AB := by euclid_finish
  euclid_finish

end Elements.Book1

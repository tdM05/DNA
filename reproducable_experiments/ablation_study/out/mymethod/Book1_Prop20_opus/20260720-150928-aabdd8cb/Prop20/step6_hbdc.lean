import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_20_step6_hbdc (a b c d : Point) (AB DC : Line)
    (hbAB : b.onLine AB) (hdAB : d.onLine AB) (hbad : between b a d)
    (hcDC : c.onLine DC) (hdDC : d.onLine DC) (hcAB : ¬ c.onLine AB)
    : ¬ b.onLine DC := by
  euclid_finish

end Elements.Book1

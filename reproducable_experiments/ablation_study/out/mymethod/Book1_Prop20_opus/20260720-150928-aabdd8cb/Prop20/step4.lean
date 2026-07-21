import SystemE
import Book1.Prop05.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_20_step4 (a c d d' : Point) (AB AC DC : Line)
    (haAB : a.onLine AB) (hd'AB : d'.onLine AB) (hadd' : between a d d')
    (hdDC : d.onLine DC) (hcDC : c.onLine DC)
    (haAC : a.onLine AC) (hcAC : c.onLine AC) (hACAB : AC ≠ AB)
    (hassump1 : |(d─a)| = |(a─c)|)   -- "$DA$ is equal to $AC$"
    : ∠ a:d:c = ∠ a:c:d := by
  euclid_apply (extend_point AC a c) as e
  euclid_apply (proposition_5 a d c d' e AB DC AC)
  euclid_finish

end Elements.Book1

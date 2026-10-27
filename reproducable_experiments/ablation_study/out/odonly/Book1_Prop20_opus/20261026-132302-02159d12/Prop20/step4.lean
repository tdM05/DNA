import SystemE
import Book1.Prop05.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_20_step4 (a c d d' : Point) (AB DC AC : Line)
  (hassump1 : |(d─a)| = |(a─c)|)   -- "$DA$ is equal to $AC$"
  (haAB : a.onLine AB) (hd'AB : d'.onLine AB) (hadd' : between a d d')
  (hdDC : d.onLine DC) (hcDC : c.onLine DC)
  (hcAC : c.onLine AC) (haAC : a.onLine AC) (hACAB : AC ≠ AB)
  : ∠ a:d:c = ∠ a:c:d := by
  euclid_apply (extend_point AC a c) as e
  euclid_apply (proposition_5 a d c d' e AB DC AC)
  euclid_finish

end Elements.Book1

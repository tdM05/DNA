import SystemE
import Book1.Prop13.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_14_s2
  (a b c e : Point) (AB BC : Line)
  (ha_ab : a.onLine AB) (hb_ab : b.onLine AB) (hab_ne : a ≠ b)
  (hb_bc : b.onLine BC) (hc_bc : c.onLine BC)
  (he_bc : e.onLine BC) (hc_ab : ¬c.onLine AB)
  (hcbe : between c b e)
  : ∠ a:b:c + ∠ a:b:e = ∟ + ∟ := by
  euclid_apply (proposition_13 a b e c AB BC)
  euclid_finish

end Elements.Book1

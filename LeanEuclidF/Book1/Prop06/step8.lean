import SystemE
import Book1.Prop04.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

/- 1.6.8: the triangle DBC is equal to the triangle ACB [Prop.~1.4], as an AREA equality
   (Euclid's "the triangle equal to the triangle" = equal magnitude). SAS (`proposition_4`,
   the same application as step7) puts the full congruence — base |d─c| = |a─b| plus the two
   remaining angles — into context; `area_congruence` then turns that congruence into the
   area equality area(△DBC) = area(△ACB). The "lesser to the greater" (whole > part) is the
   next sentence's job (1.6.9, C.N.5). -/
theorem helper_1_6_step8 (a b c d : Point) (AB BC AC DC : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hab : a ≠ b)
    (hbBC : b.onLine BC) (hcBC : c.onLine BC)
    (hcAC : c.onLine AC) (haAC : a.onLine AC)
    (hABneBC : AB ≠ BC) (hBCneAC : BC ≠ AC) (hACneAB : AC ≠ AB)
    (hbda : between b d a) (hdDC : d.onLine DC) (hcDC : c.onLine DC)
    (hbdac : |(b─d)| = |(a─c)|) (hdbc_acb : ∠ d:b:c = ∠ a:c:b) :
    Triangle.area △d:b:c = Triangle.area △a:c:b := by
  euclid_apply (proposition_4 b d c c a b AB DC BC AC AB BC)
  euclid_apply (area_congruence d b c a c b)
  assumption

end Elements.Book1

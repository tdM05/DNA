import SystemE
import Book1.Prop03.Main
import Book1.Prop04.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

-- Symmetric case of the reductio: AC is the greater (|a─c| > |a─b|). Mirror of steps 3–9
-- with the roles of b and c (and lines AB, AC) swapped: cut off DC = AB from the greater AC,
-- join DB, apply SAS (I.4) and area_congruence to get △DCB = △ABC, then the sum-of-areas
-- contradiction (△ADB has zero area ⟹ b on AC, impossible).
set_option systemE.solverTime 30 in
theorem helper_1_6_sym (a b c : Point) (AB BC AC : Line)
    (ha_AB : a.onLine AB) (hb_AB : b.onLine AB) (hab : a ≠ b)
    (hb_BC : b.onLine BC) (hc_BC : c.onLine BC)
    (ha_AC : a.onLine AC) (hc_AC : c.onLine AC)
    (hAB_BC : AB ≠ BC) (hBC_AC : BC ≠ AC) (hAC_AB : AC ≠ AB)
    (hang : ∠ a:b:c = ∠ a:c:b)
    (hgt : |(a─c)| > |(a─b)|) :
    False := by
  euclid_apply (proposition_3 c a a b AC AB) as d
  euclid_apply (line_from_points d b) as DB
  have sym_ang : ∠ d:c:b = ∠ a:b:c := by sorry
  have sym_area : Triangle.area △ d:c:b = Triangle.area △ a:b:c := by sorry
  have sym_false : False := by sorry
  exact sym_false

end Elements.Book1

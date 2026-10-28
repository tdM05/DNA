import SystemE
import Book1.Prop03.Main
import Book1.Prop04.Main
import Book1.Prop06.sym_ang
import Book1.Prop06.sym_area
import Book1.Prop06.sym_false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

-- Symmetric case of the reductio: AC is the greater (|a─c| > |a─b|). Mirror of steps 3–9
-- with the roles of b and c (and lines AB, AC) swapped: cut off DC = AB from the greater AC,
-- join DB, apply SAS (I.4) and area_congruence to get △DCB = △ABC, then the sum-of-areas
-- contradiction (△ADB has zero area ⟹ b on AC, impossible).
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
  have sym_ang : ∠ d:c:b = ∠ a:b:c := by euclid_apply (helper_1_6_sym_ang a b c d AB BC AC (by euclid_assumption "" (show between c d a; assumption)) (by euclid_assumption "" (show ∠ a:b:c = ∠ a:c:b; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show AB ≠ BC; assumption)) (by euclid_assumption "" (show BC ≠ AC; assumption)) (by euclid_assumption "" (show AC ≠ AB; assumption)))
  have sym_area : Triangle.area △ d:c:b = Triangle.area △ a:b:c := by euclid_apply (helper_1_6_sym_area a b c d AB BC AC DB (by euclid_assumption "" (show between c d a; assumption)) (by euclid_assumption "" (show |(c─d)| = |(a─b)|; assumption)) (by euclid_assumption "" (show ∠ d:c:b = ∠ a:b:c; assumption)) (by euclid_assumption "" (show d.onLine DB; assumption)) (by euclid_assumption "" (show b.onLine DB; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show AB ≠ BC; assumption)) (by euclid_assumption "" (show BC ≠ AC; assumption)) (by euclid_assumption "" (show AC ≠ AB; assumption)))
  have sym_false : False := by euclid_apply (helper_1_6_sym_false a b c d AB BC AC (by euclid_assumption "" (show between c d a; assumption)) (by euclid_assumption "" (show Triangle.area △ d:c:b = Triangle.area △ a:b:c; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show AB ≠ BC; assumption)) (by euclid_assumption "" (show BC ≠ AC; assumption)) (by euclid_assumption "" (show AC ≠ AB; assumption)))
  exact sym_false

end Elements.Book1

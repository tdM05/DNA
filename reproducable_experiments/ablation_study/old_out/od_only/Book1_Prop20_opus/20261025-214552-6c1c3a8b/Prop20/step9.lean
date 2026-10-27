import SystemE
import Book1.Prop03.Main
import Book1.Prop20.step9_bet
import Book1.Prop20.step9_iso
import Book1.Prop20.step9_gt
import Book1.Prop20.step9_form
import Book1.Prop20.step9_big
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_20_step9 (a b c : Point) (AB BC AC : Line)
    (h_aAB : a.onLine AB) (h_bAB : b.onLine AB) (h_ab : a ≠ b)
    (h_bBC : b.onLine BC) (h_cBC : c.onLine BC)
    (h_cAC : c.onLine AC) (h_aAC : a.onLine AC)
    (h_ABBC : AB ≠ BC) (h_BCAC : BC ≠ AC) (h_ACAB : AC ≠ AB) :
    |(a─b)| + |(b─c)| > |(a─c)| := by
  euclid_apply (extend_point_longer AB a b (b─c)) as d2'
  euclid_apply (proposition_3 b d2' b c AB BC) as d2
  euclid_apply (line_from_points d2 c) as D2C
  have step9_bet : between a b d2 := by euclid_apply (helper_1_20_step9_bet a b d2 d2' AB (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show d2'.onLine AB; assumption)) (by euclid_assumption "" (show between a b d2'; assumption)) (by euclid_assumption "" (show between b d2 d2'; assumption)))
  have step9_iso : ∠ b:d2:c = ∠ b:c:d2 := by euclid_apply (helper_1_20_step9_iso a b c d2 d2' AB BC AC D2C (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show AB ≠ BC; assumption)) (by euclid_assumption "" (show BC ≠ AC; assumption)) (by euclid_assumption "" (show AC ≠ AB; assumption)) (by euclid_assumption "" (show d2'.onLine AB; assumption)) (by euclid_assumption "" (show between a b d2'; assumption)) (by euclid_assumption "" (show between b d2 d2'; assumption)) (by euclid_assumption "" (show d2.onLine D2C; assumption)) (by euclid_assumption "" (show c.onLine D2C; assumption)) (by euclid_assumption "" (show |(b─d2)| = |(b─c)|; assumption)))
  have step9_gt : ∠ a:c:d2 > ∠ a:d2:c := by euclid_apply (helper_1_20_step9_gt a b c d2 d2' AB BC AC D2C (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show AB ≠ BC; assumption)) (by euclid_assumption "" (show BC ≠ AC; assumption)) (by euclid_assumption "" (show AC ≠ AB; assumption)) (by euclid_assumption "" (show d2'.onLine AB; assumption)) (by euclid_assumption "" (show between b d2 d2'; assumption)) (by euclid_assumption "" (show d2.onLine D2C; assumption)) (by euclid_assumption "" (show c.onLine D2C; assumption)) (by euclid_assumption "" (show between a b d2; assumption)) (by euclid_assumption "" (show ∠ b:d2:c = ∠ b:c:d2; assumption)))
  have step9_form : formTriangle a c d2 AC D2C AB := by euclid_apply (helper_1_20_step9_form a b c d2 d2' AB BC AC D2C (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show AB ≠ BC; assumption)) (by euclid_assumption "" (show BC ≠ AC; assumption)) (by euclid_assumption "" (show AC ≠ AB; assumption)) (by euclid_assumption "" (show d2'.onLine AB; assumption)) (by euclid_assumption "" (show between a b d2'; assumption)) (by euclid_assumption "" (show between b d2 d2'; assumption)) (by euclid_assumption "" (show d2.onLine D2C; assumption)) (by euclid_assumption "" (show c.onLine D2C; assumption)))
  have step9_big : |(a─d2)| > |(a─c)| := by euclid_apply (helper_1_20_step9_big a c d2 AB AC D2C (by euclid_assumption "" (show formTriangle a c d2 AC D2C AB; assumption)) (by euclid_assumption "" (show ∠ a:c:d2 > ∠ a:d2:c; assumption)))
  euclid_finish

end Elements.Book1

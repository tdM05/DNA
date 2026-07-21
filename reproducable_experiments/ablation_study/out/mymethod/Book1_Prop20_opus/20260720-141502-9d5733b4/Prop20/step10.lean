import SystemE
import Book1.Prop03.Main
import Book1.Prop20.step10_iso
import Book1.Prop20.step10_gt
import Book1.Prop20.step10_big
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

-- Case 3: |BC| + |CA| > |AB|.  Extend BC beyond C to F with CF = CA (apex C),
-- join FA, then triangle FAB gives FB > BA, and FB = BC + CF = BC + CA.
theorem helper_1_20_step10 (a b c : Point) (AB BC AC : Line)
    (ha_AB : a.onLine AB) (hb_AB : b.onLine AB) (hab : a ≠ b)
    (hb_BC : b.onLine BC) (hc_BC : c.onLine BC)
    (hc_AC : c.onLine AC) (ha_AC : a.onLine AC)
    (hABBC : AB ≠ BC) (hBCAC : BC ≠ AC) (hACAB : AC ≠ AB) :
    |(b─c)| + |(c─a)| > |(a─b)| := by
  euclid_apply (extend_point_longer BC b c (c─a)) as f'
  euclid_apply (proposition_3 c f' c a BC AC) as f
  euclid_apply (line_from_points f a) as FA
  have step10_iso : ∠ c:f:a = ∠ c:a:f := by euclid_apply (helper_1_20_step10_iso a b c f f' AB BC AC FA (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show AB ≠ BC; assumption)) (by euclid_assumption "" (show BC ≠ AC; assumption)) (by euclid_assumption "" (show AC ≠ AB; assumption)) (by euclid_assumption "" (show f'.onLine BC; assumption)) (by euclid_assumption "" (show between c f f'; assumption)) (by euclid_assumption "" (show |(c─f)| = |(c─a)|; assumption)) (by euclid_assumption "" (show f.onLine FA; assumption)) (by euclid_assumption "" (show a.onLine FA; assumption)))
  have step10_gt  : ∠ b:a:f > ∠ c:f:a := by euclid_apply (helper_1_20_step10_gt a b c f f' AB BC AC FA (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show AB ≠ BC; assumption)) (by euclid_assumption "" (show BC ≠ AC; assumption)) (by euclid_assumption "" (show AC ≠ AB; assumption)) (by euclid_assumption "" (show f'.onLine BC; assumption)) (by euclid_assumption "" (show between b c f'; assumption)) (by euclid_assumption "" (show between c f f'; assumption)) (by euclid_assumption "" (show f.onLine FA; assumption)) (by euclid_assumption "" (show a.onLine FA; assumption)) (by euclid_assumption "" (show ∠ c:f:a = ∠ c:a:f; assumption)))
  have step10_big : |(f─b)| > |(b─a)| := by euclid_apply (helper_1_20_step10_big a b c f f' AB BC AC FA (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show AB ≠ BC; assumption)) (by euclid_assumption "" (show BC ≠ AC; assumption)) (by euclid_assumption "" (show AC ≠ AB; assumption)) (by euclid_assumption "" (show f'.onLine BC; assumption)) (by euclid_assumption "" (show between b c f'; assumption)) (by euclid_assumption "" (show between c f f'; assumption)) (by euclid_assumption "" (show f.onLine FA; assumption)) (by euclid_assumption "" (show a.onLine FA; assumption)) (by euclid_assumption "" (show ∠ b:a:f > ∠ c:f:a; assumption)))
  euclid_finish

end Elements.Book1

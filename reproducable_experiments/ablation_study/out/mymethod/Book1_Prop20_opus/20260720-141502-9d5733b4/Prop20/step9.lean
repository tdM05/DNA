import SystemE
import Book1.Prop03.Main
import Book1.Prop20.step9_iso
import Book1.Prop20.step9_gt
import Book1.Prop20.step9_big
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

-- Case 2: |AB| + |BC| > |AC|.  Extend AB beyond B to E with BE = BC (apex B),
-- join EC, then triangle ECA gives EA > AC, and EA = AB + BE = AB + BC.
theorem helper_1_20_step9 (a b c : Point) (AB BC AC : Line)
    (ha_AB : a.onLine AB) (hb_AB : b.onLine AB) (hab : a ≠ b)
    (hb_BC : b.onLine BC) (hc_BC : c.onLine BC)
    (hc_AC : c.onLine AC) (ha_AC : a.onLine AC)
    (hABBC : AB ≠ BC) (hBCAC : BC ≠ AC) (hACAB : AC ≠ AB) :
    |(a─b)| + |(b─c)| > |(a─c)| := by
  euclid_apply (extend_point_longer AB a b (b─c)) as e'
  euclid_apply (proposition_3 b e' b c AB BC) as e
  euclid_apply (line_from_points e c) as EC
  have step9_iso : ∠ b:e:c = ∠ b:c:e := by euclid_apply (helper_1_20_step9_iso a b c e e' AB BC AC EC (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show AB ≠ BC; assumption)) (by euclid_assumption "" (show BC ≠ AC; assumption)) (by euclid_assumption "" (show AC ≠ AB; assumption)) (by euclid_assumption "" (show e'.onLine AB; assumption)) (by euclid_assumption "" (show between b e e'; assumption)) (by euclid_assumption "" (show |(b─e)| = |(b─c)|; assumption)) (by euclid_assumption "" (show e.onLine EC; assumption)) (by euclid_assumption "" (show c.onLine EC; assumption)))
  have step9_gt  : ∠ a:c:e > ∠ b:e:c := by euclid_apply (helper_1_20_step9_gt a b c e e' AB BC AC EC (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show AB ≠ BC; assumption)) (by euclid_assumption "" (show BC ≠ AC; assumption)) (by euclid_assumption "" (show AC ≠ AB; assumption)) (by euclid_assumption "" (show e'.onLine AB; assumption)) (by euclid_assumption "" (show between a b e'; assumption)) (by euclid_assumption "" (show between b e e'; assumption)) (by euclid_assumption "" (show e.onLine EC; assumption)) (by euclid_assumption "" (show c.onLine EC; assumption)) (by euclid_assumption "" (show ∠ b:e:c = ∠ b:c:e; assumption)))
  have step9_big : |(e─a)| > |(a─c)| := by euclid_apply (helper_1_20_step9_big a b c e e' AB BC AC EC (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show AB ≠ BC; assumption)) (by euclid_assumption "" (show BC ≠ AC; assumption)) (by euclid_assumption "" (show AC ≠ AB; assumption)) (by euclid_assumption "" (show e'.onLine AB; assumption)) (by euclid_assumption "" (show between a b e'; assumption)) (by euclid_assumption "" (show between b e e'; assumption)) (by euclid_assumption "" (show e.onLine EC; assumption)) (by euclid_assumption "" (show c.onLine EC; assumption)) (by euclid_assumption "" (show ∠ a:c:e > ∠ b:e:c; assumption)))
  euclid_finish

end Elements.Book1

import SystemE
import Book1.Prop19.Main
import Book1.Prop20.step6_form
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_20_step6 (a b c d d' : Point) (AB BC AC DC : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hab : a ≠ b) (hd'AB : d'.onLine AB) (hadd' : between a d d')
    (hbad : between b a d)
    (hbBC : b.onLine BC) (hcBC : c.onLine BC)
    (hcDC : c.onLine DC) (hdDC : d.onLine DC)
    (hcAC : c.onLine AC) (haAC : a.onLine AC)
    (hABBC : AB ≠ BC) (hBCAC : BC ≠ AC) (hACAB : AC ≠ AB)
    (hassump1 : ∠ b:c:d > ∠ b:d:c)   -- "$DCB$ is a triangle having the angle $BCD$ greater than $BDC$"
    : |(d─b)| > |(b─c)| := by
  have step6_form : formTriangle b c d BC DC AB := by euclid_apply (helper_1_20_step6_form a b c d d' AB BC AC DC (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show d'.onLine AB; assumption)) (by euclid_assumption "" (show between a d d'; assumption)) (by euclid_assumption "" (show between b a d; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine DC; assumption)) (by euclid_assumption "" (show d.onLine DC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show AB ≠ BC; assumption)) (by euclid_assumption "" (show BC ≠ AC; assumption)) (by euclid_assumption "" (show AC ≠ AB; assumption)))
  have hang : ∠ b:c:d > ∠ c:d:b := by euclid_finish
  euclid_apply (proposition_19 b c d BC DC AB)
  euclid_finish

end Elements.Book1

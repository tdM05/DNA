import SystemE
import Book1.Prop19.Main
import Book1.Prop20.step6_form
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_20_step6 (a b c d d' : Point) (AB BC AC DC : Line)
    (h_aAB : a.onLine AB) (h_bAB : b.onLine AB) (h_ab : a ≠ b)
    (h_bBC : b.onLine BC) (h_cBC : c.onLine BC)
    (h_cAC : c.onLine AC) (h_aAC : a.onLine AC)
    (h_ABBC : AB ≠ BC) (h_BCAC : BC ≠ AC) (h_ACAB : AC ≠ AB)
    (h_dpAB : d'.onLine AB) (h_bad' : between b a d') (h_add' : between a d d')
    (h_dDC : d.onLine DC) (h_cDC : c.onLine DC)
    (hassump1 : ∠ b:c:d > ∠ b:d:c) :
    |(d─b)| > |(b─c)| := by
  have step6_form : formTriangle b c d BC DC AB := by euclid_apply (helper_1_20_step6_form a b c d d' AB BC AC DC (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show AB ≠ BC; assumption)) (by euclid_assumption "" (show BC ≠ AC; assumption)) (by euclid_assumption "" (show AC ≠ AB; assumption)) (by euclid_assumption "" (show d'.onLine AB; assumption)) (by euclid_assumption "" (show between b a d'; assumption)) (by euclid_assumption "" (show between a d d'; assumption)) (by euclid_assumption "" (show d.onLine DC; assumption)) (by euclid_assumption "" (show c.onLine DC; assumption)))
  euclid_apply (proposition_19 b c d BC DC AB)
  euclid_finish

end Elements.Book1

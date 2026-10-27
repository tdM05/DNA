import SystemE
import Book1.Prop16.Main
import Book1.Prop18.step3_tri
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_18_step3 (a b c d : Point) (AB BC AC BD : Line)
  (hbBC : b.onLine BC) (hcBC : c.onLine BC)
  (hbAB : b.onLine AB) (haAB : a.onLine AB) (hab : a ≠ b)
  (hcAC : c.onLine AC) (haAC : a.onLine AC)
  (hBCAC : BC ≠ AC) (hACAB : AC ≠ AB)
  (hbd : distinctPointsOnLine b d BD)
  -- Reasoning hypotheses (from @assumption — keep these types in the signature):
  (hassump1 : between a d c)   -- "angle $ADB$ is external to triangle $BCD$"
  : ∠ a:d:b > ∠ d:c:b := by
  have step3_tri : formTriangle b c d BC AC BD := by euclid_apply (helper_1_18_step3_tri a b c d AB BC AC BD (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show BC ≠ AC; assumption)) (by euclid_assumption "" (show AC ≠ AB; assumption)) (by euclid_assumption "" (show distinctPointsOnLine b d BD; assumption)) (by euclid_assumption "" (show between a d c; assumption)))
  euclid_apply (proposition_16 b c d a BC AC BD)
  euclid_finish

end Elements.Book1

import SystemE
import Book1.Prop17.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_47_hoffBD
    (a b c d : Point) (AB BC AC BD : Line)
    (hbac : ∠ b:a:c = ∟)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hab : a ≠ b)
    (hbBC : b.onLine BC) (hcBC : c.onLine BC) (haoffBC : ¬a.onLine BC)
    (hcAC : c.onLine AC) (haAC : a.onLine AC)
    (hABBC : AB ≠ BC) (hBCAC : BC ≠ AC) (hACAB : AC ≠ AB)
    (hbBD : b.onLine BD) (hdBD : d.onLine BD)
    (hcbd : ∠ c:b:d = ∟) (hdopp : ¬d.sameSide a BC) (hdoffBC : ¬d.onLine BC) :
    ¬(a.onLine BD) := by
  intro haBD
  euclid_apply (two_points_determine_line a b AB BD)
  euclid_apply (pasch_4 a b d BC AB)
  euclid_apply (flat_angle_onlyif a b d)
  euclid_apply (proposition_17 c a b AC AB BC)
  euclid_finish

end Elements.Book1

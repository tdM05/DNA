import SystemE
import Book1.Prop47.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_12_step5 (a b c d : Point) (AB BC CA : Line)
    (ha_AB : a.onLine AB) (hb_AB : b.onLine AB)
    (hb_BC : b.onLine BC) (hc_BC : c.onLine BC)
    (hc_CA : c.onLine CA) (ha_CA : a.onLine CA) (hd_CA : d.onLine CA)
    (hab : a ≠ b) (hABBC : AB ≠ BC) (hBCCA : BC ≠ CA) (hCAAB : CA ≠ AB)
    (hbtw : between d a c)
    (hassump1 : ∠ b:d:c = ∟) :
    |(a─b)| * |(a─b)| = |(a─d)| * |(a─d)| + |(d─b)| * |(d─b)| := by
  euclid_apply (line_from_points d b) as DB
  euclid_apply (equal_angles d b b a c DB CA)
  euclid_apply (Elements.Book1.proposition_47 d a b CA AB DB)
  euclid_finish

end Elements.Book2

import SystemE
import Book1.Prop47.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_12_step5
  (a b c d : Point) (AB BC CA : Line)
  (ha_AB : a.onLine AB) (hb_AB : b.onLine AB)
  (ha_CA : a.onLine CA) (hc_CA : c.onLine CA) (hd_CA : d.onLine CA)
  (hb_BC : b.onLine BC) (hc_BC : c.onLine BC)
  (hab : a ≠ b) (hCAAB : CA ≠ AB) (hBCCA : BC ≠ CA)
  (hbetween : between d a c)
  (hassump1 : ∠ b:d:c = ∟)
  : |(a─b)| * |(a─b)| = |(a─d)| * |(a─d)| + |(d─b)| * |(d─b)| := by
  have hdb : d ≠ b := by euclid_finish
  euclid_apply (line_from_points d b) as DB
  euclid_apply (equal_angles d b b a c DB CA)
  have hadb : ∠ a:d:b = ∟ := by euclid_finish
  euclid_apply (Elements.Book1.proposition_47 d a b CA AB DB)
  assumption

end Elements.Book2

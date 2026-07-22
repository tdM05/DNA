import SystemE
import Book1.Prop47.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_12_step5
  (a b c d : Point) (AB BC CA : Line)
  (hbAB : b.onLine AB) (haAB : a.onLine AB)
  (hbBC : b.onLine BC) (hcBC : c.onLine BC)
  (hcCA : c.onLine CA) (haCA : a.onLine CA) (hdCA : d.onLine CA)
  (hABBC : AB ≠ BC) (hBCCA : BC ≠ CA) (hCAAB : CA ≠ AB)
  (hbet : between d a c)
  (hangle : ∠ b:d:c = ∟)
  : |(a─b)| * |(a─b)| = |(a─d)| * |(a─d)| + |(d─b)| * |(d─b)| := by
  euclid_apply (line_from_points d b) as DB
  euclid_apply (Elements.Book1.proposition_47 d a b CA AB DB)
  euclid_finish

end Elements.Book2

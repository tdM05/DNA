import SystemE
import Book1.Prop47.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_12_step5
  (a b c d : Point) (AB BC CA : Line)
  (hab_a : a.onLine AB) (hab_b : b.onLine AB) (hab_ne : a ≠ b)
  (hbc_b : b.onLine BC) (hbc_c : c.onLine BC)
  (hca_c : c.onLine CA) (hca_a : a.onLine CA)
  (hAB_BC : AB ≠ BC) (hBC_CA : BC ≠ CA) (hCA_AB : CA ≠ AB)
  (hd : d.onLine CA)
  (hbetween : between d a c)
  (hrt : ∠ b:d:c = ∟)
  : |(a─b)| * |(a─b)| = |(a─d)| * |(a─d)| + |(d─b)| * |(d─b)| := by
  euclid_apply (line_from_points d b) as DB
  euclid_apply (Elements.Book1.proposition_47 d a b CA AB DB)
  euclid_finish

end Elements.Book2

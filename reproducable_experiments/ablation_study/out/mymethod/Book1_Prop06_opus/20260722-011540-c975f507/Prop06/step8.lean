import SystemE
import Book1.Prop04.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_6_step8 (a b c d : Point) (AB BC AC DC : Line)
  (h_a_AB : a.onLine AB) (h_b_AB : b.onLine AB) (h_ab : a ≠ b)
  (h_b_BC : b.onLine BC) (h_c_BC : c.onLine BC)
  (h_c_AC : c.onLine AC) (h_a_AC : a.onLine AC)
  (h_AB_BC : AB ≠ BC) (h_BC_AC : BC ≠ AC) (h_AC_AB : AC ≠ AB)
  (hbet : between b d a)
  (hd_DC : d.onLine DC) (hc_DC : c.onLine DC)
  (hstep5 : |(d─b)| = |(a─c)| ∧ |(b─c)| = |(c─b)|)
  (h6 : ∠ d:b:c = ∠ a:c:b)
  : |(d─c)| = |(a─b)| ∧ (∠ b:d:c = ∠ c:a:b) ∧ (∠ b:c:d = ∠ c:b:a) := by
  obtain ⟨h5a, h5b⟩ := hstep5
  euclid_apply (proposition_4 b d c c a b AB DC BC AC AB BC)
  euclid_finish

end Elements.Book1

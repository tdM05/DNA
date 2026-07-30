import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_33_s7
  (a b c d : Point) (BC : Line)
  (h_b_BC : b.onLine BC) (h_c_BC : c.onLine BC)
  (h_bd : b ≠ d)
  (s1 : distinctPointsOnLine b c BC)
  (s6 : ∠ b:a:c = ∠ c:d:b ∧ ∠ a:c:b = ∠ d:b:c)
  : ∠ a:c:b = ∠ c:b:d := by
  have h_bc : b ≠ c := s1.right.right
  have hrev : ∠ d:b:c = ∠ c:b:d := by euclid_finish
  exact s6.right.trans hrev

end Elements.Book1

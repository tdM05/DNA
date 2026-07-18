import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_47_step6_sum
    (a b c h : Point) (BC : Line)
    (hab : a ≠ b) (hcBC : c.onLine BC) (haoffBC : ¬a.onLine BC)
    (hbac : ∠ b:a:c = ∟) (hcah : ∠ c:a:h = ∟) :
    ∠ c:a:b + ∠ c:a:h = ∟ + ∟ := by
  have hac : a ≠ c := by euclid_finish
  euclid_apply (angle_symm b a c)
  have hcab : ∠ c:a:b = ∟ := by euclid_finish
  linarith [hcab, hcah]

end Elements.Book1

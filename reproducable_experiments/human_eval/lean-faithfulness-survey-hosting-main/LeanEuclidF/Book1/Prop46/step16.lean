import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_46_s16
    (a b d e : Point) (AB AD BE DE : Line)
    (s5 : formParallelogram d e a b DE AB AD BE)
    (s13 : ∠ b:a:d = ∟)
    (s14 : ∠ a:d:e = ∟)
    (s15 : formParallelogram d e a b DE AB AD BE →
      (|(a─b)| = |(d─e)| ∧ |(a─d)| = |(b─e)| ∧ ∠ b:a:d = ∠ b:e:d ∧ ∠ a:d:e = ∠ a:b:e)) :
    ∠ a:b:e = ∟ ∧ ∠ b:e:d = ∟ := by
  have h34 := s15 s5
  exact ⟨by linarith [h34.2.2.2, s14], by linarith [h34.2.2.1, s13]⟩

end Elements.Book1

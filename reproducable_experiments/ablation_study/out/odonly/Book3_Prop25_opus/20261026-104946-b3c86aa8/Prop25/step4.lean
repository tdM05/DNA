import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_step4 (a b d : Point) :
    ∠ a:b:d > ∠ b:a:d ∨ ∠ a:b:d = ∠ b:a:d ∨ ∠ a:b:d < ∠ b:a:d := by
  rcases lt_trichotomy (∠ a:b:d) (∠ b:a:d) with h | h | h
  · right; right; exact h
  · right; left; exact h
  · left; exact h

end Elements.Book3

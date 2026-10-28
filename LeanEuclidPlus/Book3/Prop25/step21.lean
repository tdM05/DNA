import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_step21 (a b d e : Point) (DB : Line) (heDB : e.onLine DB)
  -- Reasoning hypotheses (from @assumption — keep these types in the signature):
  (hassump1 : ∠ a:b:d < ∠ b:a:d)   -- "$ABD$ is less than $BAD$"
  (hassump2 : ∠ b:a:e = ∠ a:b:d)   -- "we construct (angle $BAE$), equal to angle $ABD$, on the straight-line $BA$, at the point $A$ on it [Prop.~1.23]"
  : e.onLine DB := by
  exact heDB

end Elements.Book3

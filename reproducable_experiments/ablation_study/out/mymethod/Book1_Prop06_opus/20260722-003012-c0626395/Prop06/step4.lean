import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_6_step4
  (c d : Point) (DC : Line)
  (hd : d.onLine DC) (hc : c.onLine DC)
  : d.onLine DC ∧ c.onLine DC := by
  exact ⟨hd, hc⟩

end Elements.Book1

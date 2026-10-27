import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_3_step3 (a : Point) (AF CD : Line)
    (h_a_AF : a.onLine AF) (h_AF_CD : ¬(AF.intersectsLine CD)) :
    a.onLine AF ∧ ¬(AF.intersectsLine CD) := by
  exact ⟨h_a_AF, h_AF_CD⟩

end Elements.Book2

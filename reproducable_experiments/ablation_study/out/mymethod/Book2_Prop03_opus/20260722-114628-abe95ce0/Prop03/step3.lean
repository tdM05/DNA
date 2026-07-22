import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_3_step3 (a : Point) (AF CD : Line)
    (ha_af : a.onLine AF) (hpar : ¬(AF.intersectsLine CD)) :
    a.onLine AF ∧ ¬(AF.intersectsLine CD) :=
  ⟨ha_af, hpar⟩

end Elements.Book2

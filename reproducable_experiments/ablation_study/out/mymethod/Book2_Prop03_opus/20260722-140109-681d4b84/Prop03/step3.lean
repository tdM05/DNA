import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_3_step3 (a : Point) (AF CD : Line)
    (haAF : a.onLine AF) (hAFparCD : ¬(AF.intersectsLine CD)) :
    a.onLine AF ∧ ¬(AF.intersectsLine CD) := by
  exact ⟨haAF, hAFparCD⟩

end Elements.Book2

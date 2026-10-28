import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_3_step3
    (a : Point) (AF CD BE : Line)
    (ha_AF : a.onLine AF) (hpar_AFCD : ¬AF.intersectsLine CD) :
    a.onLine AF ∧ (¬(AF.intersectsLine CD) ∨ ¬(AF.intersectsLine BE)) := by
  exact ⟨ha_AF, Or.inl hpar_AFCD⟩

end Elements.Book2

import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_40_s3 (a : Point) (AF BC : Line)
    (haAF : a.onLine AF) (hnAF : ¬AF.intersectsLine BC) :
    a.onLine AF ∧ ¬(AF.intersectsLine BC) := by
  exact ⟨haAF, hnAF⟩

end Elements.Book1

import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_3_step4_safbe (a f : Point) (BE AF : Line)
    (ha_AF : a.onLine AF) (hf_AF : f.onLine AF)
    (ha_off_be : ¬a.onLine BE) (hf_off_be : ¬f.onLine BE)
    (h_afbe : ¬(AF.intersectsLine BE)) :
    a.sameSide f BE := by
  by_contra hcon
  have hopp : a.opposingSides f BE := ⟨ha_off_be, hf_off_be, hcon⟩
  -- a,f on AF opposing across BE ⟹ AF meets BE, contradiction
  euclid_apply (intersection_lines_opposing a f BE AF)
  euclid_finish

end Elements.Book2

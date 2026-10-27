import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_3_step5_sbeaf (a b e f : Point) (AF BE : Line)
    (ha_AF : a.onLine AF)
    (hb_BE : b.onLine BE) (he_BE : e.onLine BE)
    (h_afbe : ¬(AF.intersectsLine BE))
    (ha_off_be : ¬a.onLine BE)
    (h_eb : e ≠ b) :
    b.sameSide e AF := by
  -- AF ≠ BE (a ∈ AF, a ∉ BE)
  have hAFBEne : AF ≠ BE := by intro h; rw [h] at ha_AF; exact ha_off_be ha_AF
  -- b off AF (else b ∈ AF ∩ BE ⟹ AF meets BE)
  have hb_off : ¬b.onLine AF := by
    intro hb
    euclid_apply (intersection_lines_common_point b AF BE)
    euclid_finish
  -- e off AF similarly
  have he_off : ¬e.onLine AF := by
    intro he
    euclid_apply (intersection_lines_common_point e AF BE)
    euclid_finish
  by_contra hcon
  have hopp : b.opposingSides e AF := ⟨hb_off, he_off, hcon⟩
  euclid_apply (intersection_lines_opposing b e AF BE)
  euclid_finish

end Elements.Book2

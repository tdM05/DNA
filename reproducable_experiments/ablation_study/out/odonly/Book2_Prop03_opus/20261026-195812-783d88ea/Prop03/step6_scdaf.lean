import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_3_step6_scdaf (c d f : Point) (CD AF : Line)
    (hc_CD : c.onLine CD) (hd_CD : d.onLine CD)
    (hf_AF : f.onLine AF)
    (h_AF_CD : ¬AF.intersectsLine CD)
    (hf_off_cd : ¬f.onLine CD) :
    c.sameSide d AF := by
  -- AF ≠ CD (f ∈ AF, f ∉ CD)
  have hAFCDne : AF ≠ CD := by intro h; rw [h] at hf_AF; exact hf_off_cd hf_AF
  -- c, d off AF (else they'd be common points of AF and CD)
  have hc_off : ¬c.onLine AF := by
    intro hc
    euclid_apply (intersection_lines_common_point c AF CD)
    euclid_finish
  have hd_off : ¬d.onLine AF := by
    intro hd
    euclid_apply (intersection_lines_common_point d AF CD)
    euclid_finish
  by_contra hcon
  have hopp : c.opposingSides d AF := ⟨hc_off, hd_off, hcon⟩
  euclid_apply (intersection_lines_opposing c d AF CD)
  euclid_finish

end Elements.Book2

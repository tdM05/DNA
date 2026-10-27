import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_3_step2_hbe (b c d e : Point) (CD BE : Line)
    (hc_CD : c.onLine CD) (hd_CD : d.onLine CD)
    (hb_BE : b.onLine BE) (he_BE : e.onLine BE)
    (h_CD_BE : ¬CD.intersectsLine BE)
    (hdc_BE : d.sameSide c BE)
    (h_eb : e ≠ b) :
    b.sameSide e CD := by
  -- c is off line BE (d.sameSide c BE ⟹ c ∉ BE)
  have hc_off_BE : ¬c.onLine BE := by euclid_finish
  -- hence CD ≠ BE (c ∈ CD but c ∉ BE)
  have hCDne : CD ≠ BE := by
    intro h; rw [h] at hc_CD; exact hc_off_BE hc_CD
  -- b is off CD (else b ∈ CD ∩ BE ⟹ CD intersects BE)
  have hb_off : ¬b.onLine CD := by
    intro hb
    euclid_apply (intersection_lines_common_point b CD BE)
    euclid_finish
  -- e is off CD similarly
  have he_off : ¬e.onLine CD := by
    intro he
    euclid_apply (intersection_lines_common_point e CD BE)
    euclid_finish
  by_contra hcon
  have hopp : b.opposingSides e CD := ⟨hb_off, he_off, hcon⟩
  euclid_apply (intersection_lines_opposing b e CD BE)
  euclid_finish

end Elements.Book2

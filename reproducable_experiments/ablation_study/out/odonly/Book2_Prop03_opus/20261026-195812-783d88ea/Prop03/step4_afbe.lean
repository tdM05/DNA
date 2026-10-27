import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_3_step4_afbe (a c d : Point) (CD BE AF : Line)
    (ha_AF : a.onLine AF)
    (hc_CD : c.onLine CD)
    (hdc_BE : d.sameSide c BE)
    (h_AF_CD : ¬AF.intersectsLine CD)
    (h_CD_BE : ¬CD.intersectsLine BE)
    (ha_off_be : ¬a.onLine BE) :
    ¬(AF.intersectsLine BE) := by
  intro hcon
  -- extract a common point p of AF and BE
  euclid_apply (intersection_lines AF BE) as p
  -- CD ≠ BE (c ∈ CD, c ∉ BE from d.sameSide c BE)
  have hCDBEne : CD ≠ BE := by
    intro h; rw [h] at hc_CD; euclid_finish
  -- p is off CD (else p ∈ CD∩BE ⟹ CD meets BE)
  have hp_off : ¬p.onLine CD := by
    intro hp
    euclid_apply (intersection_lines_common_point p CD BE)
    euclid_finish
  -- two lines through p both parallel to CD must coincide ⟹ AF = BE
  euclid_apply (parallel_line_unique p CD AF BE)
  -- but AF ≠ BE (a ∈ AF, a ∉ BE)
  euclid_finish

end Elements.Book2

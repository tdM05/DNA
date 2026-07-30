import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_35_s4
  (a d e : Point) (AF : Line)
  (hd_AF : d.onLine AF) (he_AF : e.onLine AF)
  (hbet : between a d e)
  : distinctPointsOnLine d e AF := by
  refine ⟨hd_AF, he_AF, ?_⟩
  euclid_finish

end Elements.Book1

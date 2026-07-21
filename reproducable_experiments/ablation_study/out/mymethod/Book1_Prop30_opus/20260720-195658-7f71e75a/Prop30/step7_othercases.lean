import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_30_step7_othercases (AB CD EF : Line)
  (hABEF : ¬AB.intersectsLine EF) (hCDEF : ¬CD.intersectsLine EF)
  (hABCD : AB ≠ CD) : ¬(AB.intersectsLine CD) := by
  by_contra hcon
  euclid_apply (intersection_lines AB CD) as p
  euclid_apply (parallel_line_unique p EF AB CD)
  euclid_finish

end Elements.Book1

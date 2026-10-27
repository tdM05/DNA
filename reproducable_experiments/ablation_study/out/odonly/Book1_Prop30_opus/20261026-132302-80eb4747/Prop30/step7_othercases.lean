import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_30_step7_othercases (AB CD EF : Line)
  (hAB_CD : AB ≠ CD) (hEF_AB : EF ≠ AB) (hCD_EF2 : CD ≠ EF)
  (hAB_EF : ¬AB.intersectsLine EF) (hCD_EF : ¬CD.intersectsLine EF) :
  ¬(AB.intersectsLine CD) := by
  intro hcross
  euclid_apply (intersection_lines AB CD hcross) as p
  euclid_apply (parallel_line_unique p EF AB CD)
  euclid_finish

end Elements.Book1

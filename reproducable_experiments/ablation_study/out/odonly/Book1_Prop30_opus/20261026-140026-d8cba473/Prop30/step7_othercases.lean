import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_30_step7_othercases (AB CD EF : Line)
  (hABCD : AB ≠ CD) (hEFAB : EF ≠ AB) (hCDEF : CD ≠ EF)
  (hAB_EF : ¬AB.intersectsLine EF) (hCD_EF : ¬CD.intersectsLine EF)
  : ¬(AB.intersectsLine CD) := by
  euclid_intros
  euclid_apply (intersection_lines AB CD) as p
  euclid_apply (parallel_line_unique p EF AB CD)
  euclid_finish

end Elements.Book1

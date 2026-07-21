import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

-- The `¬between g h k` case Euclid's figure left implicit (EF need not lie between AB and CD).
-- Independent of the transversal ordering: two distinct lines both parallel to EF cannot meet,
-- else through their common point run two distinct parallels to EF (parallel_line_unique ⟹ AB = CD).
theorem helper_1_30_step7_othercases
    (AB CD EF : Line)
    (hABEF : ¬AB.intersectsLine EF) (hCDEF : ¬CD.intersectsLine EF)
    (hABCD : AB ≠ CD) (hEFAB : EF ≠ AB)
    : ¬(AB.intersectsLine CD) := by
  intro hint
  -- the supposed common point of AB and CD
  euclid_apply (intersection_lines AB CD) as x
  -- through x run two lines parallel to EF, so they coincide — contradicting AB ≠ CD
  euclid_apply (parallel_line_unique x EF AB CD)
  euclid_finish

end Elements.Book1

import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

-- @euclid_gap: Euclid reads `between g h k` off the figure (the transversal meets the
-- middle parallel EF between where it meets AB and CD). The opposite orderings of the three
-- parallels are admissible; in every such case AB ∥ CD still holds, here by the uniqueness of
-- parallels (`parallel_line_unique`): if AB met CD at p, then through p both AB and CD would be
-- parallel to EF, forcing AB = CD, contradicting AB ≠ CD.
theorem helper_1_30_step7_othercases
    (AB CD EF : Line)
    (hABCD : AB ≠ CD) (hCDEF : CD ≠ EF) (hEFAB : EF ≠ AB)
    (hAB : ¬AB.intersectsLine EF) (hCD : ¬CD.intersectsLine EF) :
    ¬(AB.intersectsLine CD) := by
  intro hint
  euclid_apply (intersection_lines AB CD) as p
  euclid_apply (parallel_line_unique p EF AB CD)
  euclid_finish

end Elements.Book1

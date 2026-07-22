import SystemE
import Book2.Prop04.Main
import Mathlib.Tactic.LinearCombination
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_12_step1
  (a c d : Point) (CA : Line)
  (h_c : c.onLine CA) (h_d : d.onLine CA)
  -- Reasoning hypotheses (from @assumption — keep these types in the signature):
  (hassump1 : between d a c)   -- "the straight-line $CD$ has been cut, at random, at point $A$"
  : |(d─c)| * |(d─c)| = |(c─a)| * |(c─a)| + |(a─d)| * |(a─d)| + 2 * (|(c─a)| * |(a─d)|) := by
  euclid_apply (Elements.Book2.proposition_4 d c a CA)
  have hca : |(c─a)| = |(a─c)| := segment_symmetric c a
  have had : |(a─d)| = |(d─a)| := segment_symmetric a d
  rw [hca, had]
  linear_combination h

end Elements.Book2

import SystemE
import Book2.Prop04.Main
import Mathlib.Tactic.LinearCombination
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_12_step1
  (a c d : Point) (CA : Line)
  (hd : d.onLine CA) (hc : c.onLine CA)
  -- Reasoning hypotheses (from @assumption — keep these types in the signature):
  (hassump1 : between d a c)   -- "the straight-line $CD$ has been cut, at random, at point $A$"
  : |(d─c)| * |(d─c)| = |(c─a)| * |(c─a)| + |(a─d)| * |(a─d)| + 2 * (|(c─a)| * |(a─d)|) := by
  have hda : |(d─a)| = |(a─d)| := by euclid_finish
  have hac : |(a─c)| = |(c─a)| := by euclid_finish
  euclid_apply (Elements.Book2.proposition_4 d c a CA)
  have key : |(d─c)| * |(d─c)| = |(d─a)| * |(d─a)| + |(a─c)| * |(a─c)| + 2 * (|(d─a)| * |(a─c)|) := by
    assumption
  rw [hda, hac] at key
  linear_combination key

end Elements.Book2

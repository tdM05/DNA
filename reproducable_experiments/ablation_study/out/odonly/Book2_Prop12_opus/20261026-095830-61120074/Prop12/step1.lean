import SystemE
import Book2.Prop04.Main
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_12_step1
  (a c d : Point) (CA : Line)
  (hd_on : d.onLine CA) (hc_on : c.onLine CA)
  (hassump1 : between d a c)
  : |(d─c)| * |(d─c)| = |(c─a)| * |(c─a)| + |(a─d)| * |(a─d)| + 2 * (|(c─a)| * |(a─d)|) := by
  euclid_apply (Elements.Book2.proposition_4 d c a CA)
  rw [segment_symmetric c a, segment_symmetric a d, mul_comm (|(a─c)|) (|(d─a)|)]
  linarith

end Elements.Book2

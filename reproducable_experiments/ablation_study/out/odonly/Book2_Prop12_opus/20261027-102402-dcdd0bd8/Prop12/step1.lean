import SystemE
import Book2.Prop04.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_12_step1
  (a c d : Point) (CA : Line)
  (hc : c.onLine CA) (hd : d.onLine CA)
  (hassump1 : between d a c)
  : |(d─c)| * |(d─c)| = |(c─a)| * |(c─a)| + |(a─d)| * |(a─d)| + 2 * (|(c─a)| * |(a─d)|) := by
  euclid_apply (Elements.Book2.proposition_4 d c a CA)
  have h4 : |(d─c)| * |(d─c)| = |(d─a)| * |(d─a)| + |(a─c)| * |(a─c)| + 2 * (|(d─a)| * |(a─c)|) := by assumption
  rw [segment_symmetric d a, segment_symmetric a c] at h4
  rw [h4]; ring

end Elements.Book2

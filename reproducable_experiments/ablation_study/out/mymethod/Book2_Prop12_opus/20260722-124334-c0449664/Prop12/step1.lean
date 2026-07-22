import SystemE
import Book2.Prop04.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_12_step1 (a c d : Point) (CA : Line)
    (hd : d.onLine CA) (hc : c.onLine CA)
    (hassump1 : between d a c) :
    |(d─c)| * |(d─c)| = |(c─a)| * |(c─a)| + |(a─d)| * |(a─d)| + 2 * (|(c─a)| * |(a─d)|) := by
  have e : |(d─c)| = |(c─d)| := by euclid_finish
  euclid_apply (Elements.Book2.proposition_4 c d a CA)
  rw [e]
  assumption

end Elements.Book2

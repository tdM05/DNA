import SystemE
import Book1.Prop47.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1

theorem helper_3_36_step28_p47
  (b d e : Point) (EB ED DB : Line)
  (htri : formTriangle b e d EB ED DB)
  (step28_assumption1 : ∠ e:b:d = ∟)
  : |(e─b)| * |(e─b)| + |(d─b)| * |(d─b)| = |(e─d)| * |(e─d)| := by
  euclid_apply (Elements.Book1.proposition_47 b e d EB ED DB)
  euclid_finish

end Elements.Book3

import SystemE
import Book1.Prop47.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1

theorem helper_3_36_step23_p47
  (c e f : Point) (DA EC EF : Line)
  (htri : formTriangle f c e DA EC EF)
  (step23_assumption1 : ∠ e:f:c = ∟)
  : |(e─c)| * |(e─c)| = |(f─c)| * |(f─c)| + |(e─f)| * |(e─f)| := by
  euclid_apply (Elements.Book1.proposition_47 f c e DA EC EF)
  euclid_finish

end Elements.Book3

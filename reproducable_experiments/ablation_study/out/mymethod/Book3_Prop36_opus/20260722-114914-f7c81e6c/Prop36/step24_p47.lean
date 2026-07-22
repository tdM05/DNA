import SystemE
import Book1.Prop47.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1

theorem helper_3_36_step24_p47
  (d e f : Point) (DA ED EF : Line)
  (htri : formTriangle f d e DA ED EF)
  (hdfe : ∠ d:f:e = ∟)
  : |(e─d)| * |(e─d)| = |(d─f)| * |(d─f)| + |(f─e)| * |(f─e)| := by
  euclid_apply (Elements.Book1.proposition_47 f d e DA ED EF)
  euclid_finish

end Elements.Book3

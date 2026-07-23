import SystemE
import Book1.Prop47.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step24_pyth (d e f : Point) (DA EF ED : Line)
  (step24_tri : formTriangle f e d EF ED DA)
  (step24_angle : ∠ e:f:d = ∟)
  : |(e─d)| * |(e─d)| = |(e─f)| * |(e─f)| + |(f─d)| * |(f─d)| := by
  euclid_apply (Elements.Book1.proposition_47 f e d EF ED DA ⟨step24_tri, step24_angle⟩)

end Elements.Book3

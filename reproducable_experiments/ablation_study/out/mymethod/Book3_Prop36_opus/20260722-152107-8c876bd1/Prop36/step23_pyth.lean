import SystemE
import Book1.Prop47.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step23_pyth (c e f : Point) (DA EF EC : Line)
  (step23_tri : formTriangle f e c EF EC DA)
  (hassump1 : ∠ e:f:c = ∟)
  : |(e─c)| * |(e─c)| = |(e─f)| * |(e─f)| + |(f─c)| * |(f─c)| := by
  euclid_apply (Elements.Book1.proposition_47 f e c EF EC DA ⟨step23_tri, hassump1⟩)

end Elements.Book3

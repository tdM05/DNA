import SystemE
import Book1.Prop47.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step28_pyth (b d e : Point) (EB ED DB : Line)
  (step28_tri : formTriangle b e d EB ED DB)
  (step28_angle : ∠ e:b:d = ∟)
  : |(e─d)| * |(e─d)| = |(e─b)| * |(e─b)| + |(b─d)| * |(b─d)| := by
  euclid_apply (Elements.Book1.proposition_47 b e d EB ED DB ⟨step28_tri, step28_angle⟩)

end Elements.Book3

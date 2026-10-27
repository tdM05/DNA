import SystemE
import Book1.Prop19.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_20_step9_side (a b c d : Point) (AB BC DC : Line)
    (htri : formTriangle b c d BC DC AB)
    (hangle : ∠ b:c:d > ∠ b:d:c) : |(d─b)| > |(b─c)| := by
  euclid_apply (proposition_19 b c d BC DC AB)
  euclid_finish

end Elements.Book1

import SystemE
import Book1.Prop19.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_20_step9_big (a c d2 : Point) (AB AC D2C : Line)
    (h_form : formTriangle a c d2 AC D2C AB)
    (h_gt : ∠ a:c:d2 > ∠ a:d2:c) :
    |(a─d2)| > |(a─c)| := by
  euclid_apply (proposition_19 a c d2 AC D2C AB)
  euclid_finish

end Elements.Book1

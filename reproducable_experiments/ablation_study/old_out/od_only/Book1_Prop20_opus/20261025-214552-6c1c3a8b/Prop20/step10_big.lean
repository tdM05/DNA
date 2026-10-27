import SystemE
import Book1.Prop19.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_20_step10_big (a b d3 : Point) (AB BC D3A : Line)
    (h_form : formTriangle b a d3 AB D3A BC)
    (h_gt : ∠ b:a:d3 > ∠ b:d3:a) :
    |(b─d3)| > |(b─a)| := by
  euclid_apply (proposition_19 b a d3 AB D3A BC)
  euclid_finish

end Elements.Book1

import SystemE
import Book1Variants.Prop34
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_46_s6
    (a b d e : Point) (AB AD BE DE : Line)
    (s5 : formParallelogram d e a b DE AB AD BE) :
    |(a─b)| = |(d─e)| := by
  euclid_apply (proposition_34' d e a b DE AB AD BE s5)
  euclid_finish

end Elements.Book1

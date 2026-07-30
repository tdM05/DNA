import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_46_s10
    (a b d e : Point)
    (s9 : |(b─a)| = |(a─d)| ∧ |(a─d)| = |(d─e)| ∧ |(d─e)| = |(e─b)|) :
    |(b─a)| = |(a─d)| ∧ |(a─d)| = |(d─e)| ∧ |(d─e)| = |(e─b)| :=
  s9

end Elements.Book1

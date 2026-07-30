import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_11_s7
    (d e f : Point)
    (h1 : |(f─d)| = |(d─e)|) (h2 : |(f─e)| = |(d─e)|) :
    |(d─f)| = |(f─e)| := by
  euclid_finish

end Elements.Book1

import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_9_s8 (d e f : Point)
    (h1 : |(f─d)| = |(d─e)|) (h2 : |(f─e)| = |(d─e)|) :
    |(d─f)| = |(e─f)| := by euclid_finish

end Elements.Book1

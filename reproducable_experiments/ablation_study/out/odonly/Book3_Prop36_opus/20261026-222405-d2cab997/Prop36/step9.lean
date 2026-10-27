import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step9 (d a c f b : Point)
    (hstep7 : |(d─a)| * |(d─c)| + |(f─b)| * |(f─b)| = |(f─d)| * |(f─d)|)
    (hstep8 : |(f─d)| * |(f─d)| = |(f─b)| * |(f─b)| + |(d─b)| * |(d─b)|) :
    |(d─a)| * |(d─c)| + |(f─b)| * |(f─b)| = |(f─b)| * |(f─b)| + |(d─b)| * |(d─b)| := by
  rw [hstep7]; exact hstep8

end Elements.Book3

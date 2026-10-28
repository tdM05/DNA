import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
theorem helper_2_3_step8
    (a b c d e f : Point)
    (hstep4 : Triangle.area △ a:b:e + Triangle.area △ a:e:f =
      (Triangle.area △ a:c:d + Triangle.area △ a:d:f) +
      (Triangle.area △ c:b:e + Triangle.area △ c:e:d))
    (hstep5 : Triangle.area △ a:b:e + Triangle.area △ a:e:f = |(a─b)| * |(b─c)|)
    (hstep6 : Triangle.area △ a:c:d + Triangle.area △ a:d:f = |(a─c)| * |(c─b)|)
    (hstep7 : Triangle.area △ c:b:e + Triangle.area △ c:e:d = |(c─b)| * |(c─b)|) :
    |(a─b)| * |(b─c)| = |(a─c)| * |(c─b)| + |(b─c)| * |(b─c)| := by
  have hsq : |(c─b)| * |(c─b)| = |(b─c)| * |(b─c)| := by
    have h : |(c─b)| = |(b─c)| := by euclid_finish
    rw [h]
  linarith [hstep4, hstep5, hstep6, hstep7, hsq]

end Elements.Book2

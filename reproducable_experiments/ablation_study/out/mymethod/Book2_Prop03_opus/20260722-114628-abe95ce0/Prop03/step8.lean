import SystemE
import Mathlib.Tactic.Linarith

set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements

theorem helper_2_3_step8 (a b c d e f : Point)
    (hstep4 : Triangle.area △ a:f:e + Triangle.area △ a:e:b =
      (Triangle.area △ a:f:d + Triangle.area △ a:d:c)
      + (Triangle.area △ c:d:e + Triangle.area △ c:e:b))
    (hstep5 : Triangle.area △ a:f:e + Triangle.area △ a:e:b = |(a─b)| * |(b─c)|)
    (hstep6 : Triangle.area △ a:f:d + Triangle.area △ a:d:c = |(a─c)| * |(c─b)|)
    (hstep7 : Triangle.area △ c:d:e + Triangle.area △ c:e:b = |(b─c)| * |(b─c)|) :
    |(a─b)| * |(b─c)| = |(a─c)| * |(c─b)| + |(b─c)| * |(b─c)| := by
  linarith [hstep4, hstep5, hstep6, hstep7]

end Elements.Book2

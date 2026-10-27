import SystemE
import Mathlib.Tactic.Linarith
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_3_step8 (a b c d e f : Point)
    (h_step4 : Triangle.area △ a:f:e + Triangle.area △ a:e:b =
      (Triangle.area △ a:f:d + Triangle.area △ a:d:c)
    + (Triangle.area △ c:d:e + Triangle.area △ c:e:b))
    (h_step5 : Triangle.area △ a:f:e + Triangle.area △ a:e:b = |(a─b)| * |(b─c)|)
    (h_step6 : Triangle.area △ a:f:d + Triangle.area △ a:d:c = |(a─c)| * |(c─b)|)
    (h_step7 : Triangle.area △ c:d:e + Triangle.area △ c:e:b = |(b─c)| * |(b─c)|) :
    |(a─b)| * |(b─c)| = |(a─c)| * |(c─b)| + |(b─c)| * |(b─c)| := by
  linarith [h_step4, h_step5, h_step6, h_step7]

end Elements.Book2

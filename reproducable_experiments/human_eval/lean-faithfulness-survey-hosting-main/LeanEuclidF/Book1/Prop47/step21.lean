import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_47_s21
    (a b c d e f g h k : Point)
    (s18 : Triangle.area △ b:d:e + Triangle.area △ b:e:c =
      (Triangle.area △ a:g:f + Triangle.area △ a:f:b) +
      (Triangle.area △ a:h:k + Triangle.area △ a:k:c))
    (s19 : Triangle.area △ b:d:e + Triangle.area △ b:e:c = |(b─c)| * |(b─c)|)
    (s20 : (Triangle.area △ a:g:f + Triangle.area △ a:f:b = |(b─a)| * |(b─a)|) ∧
      (Triangle.area △ a:h:k + Triangle.area △ a:k:c = |(a─c)| * |(a─c)|)) :
    |(b─c)| * |(b─c)| = |(b─a)| * |(b─a)| + |(a─c)| * |(a─c)| := by
  obtain ⟨h20a, h20b⟩ := s20
  linarith [s18, s19, h20a, h20b]

end Elements.Book1

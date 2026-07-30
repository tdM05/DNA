import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1
open Elements

theorem h_1_44_s18
    (b e f g : Point) (c₁ c₂ c₃ : Point)
    (s1_x2 : Triangle.area △ f:b:e + Triangle.area △ f:e:g = Triangle.area △ c₁:c₂:c₃)
    : Triangle.area △ f:g:e + Triangle.area △ f:e:b = Triangle.area △ c₁:c₂:c₃ := by
  euclid_finish

end Elements.Book1

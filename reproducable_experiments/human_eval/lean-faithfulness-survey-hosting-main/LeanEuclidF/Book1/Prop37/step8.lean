import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_37_s8 (a b c d e f : Point)
    (h_s5 : Triangle.area △e:b:a + Triangle.area △a:b:c = Triangle.area △d:b:c + Triangle.area △d:c:f)
    (h_s6 : Triangle.area △ a:b:c = Triangle.area △ e:a:b)
    (h_s7 : Triangle.area △ d:b:c = Triangle.area △ f:d:c) :
    Triangle.area △ a:b:c = Triangle.area △ d:b:c := by
  euclid_finish

end Elements.Book1

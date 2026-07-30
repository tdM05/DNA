import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_37_s9 (a b c d : Point)
    (h_s8 : Triangle.area △ a:b:c = Triangle.area △ d:b:c) :
    Triangle.area △ a:b:c = Triangle.area △ d:b:c :=
  h_s8

end Elements.Book1

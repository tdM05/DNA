import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_40_s6 (a b c d e : Point)
    (h : Triangle.area △ a:b:c = Triangle.area △ d:c:e) :
    Triangle.area △ a:b:c = Triangle.area △ d:c:e := h

end Elements.Book1

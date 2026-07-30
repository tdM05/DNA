import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_39_s7
    (a b c d e : Point)
    (s5 : Triangle.area △ a:b:c = Triangle.area △ e:b:c)
    (s6 : Triangle.area △ a:b:c = Triangle.area △ d:b:c)
    : Triangle.area △ d:b:c = Triangle.area △ e:b:c :=
  s6.symm.trans s5

end Elements.Book1

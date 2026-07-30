import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_43_s5
    (a b c d : Point)
    (s1 : Triangle.area △ a:b:c = Triangle.area △ a:c:d)
    : Triangle.area △ a:b:c = Triangle.area △ a:d:c := by
  euclid_finish

end Elements.Book1

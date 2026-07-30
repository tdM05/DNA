import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_39_s9
    (d e b c : Point) (AE BC : Line)
    (s7 : Triangle.area △ d:b:c = Triangle.area △ e:b:c)
    (s8 : Triangle.area △ d:b:c ≠ Triangle.area △ e:b:c)
    : AE.intersectsLine BC :=
  absurd s7 s8

end Elements.Book1

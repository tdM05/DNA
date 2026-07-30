import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_39_s10
    (d e b c : Point) (BC AD : Line) (a : Point)
    (s7 : Triangle.area △ d:b:c = Triangle.area △ e:b:c)
    (s8 : Triangle.area △ d:b:c ≠ Triangle.area △ e:b:c)
    : ∀ (L : Line), a.onLine L → L ≠ AD → L.intersectsLine BC :=
  fun _ _ _ => absurd s7 s8

end Elements.Book1

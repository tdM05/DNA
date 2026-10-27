import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_20_step9_ti_s1 (x y w w' : Point) (XY : Line)
  (h_xXY : x.onLine XY) (h_yXY : y.onLine XY) (h_w'XY : w'.onLine XY)
  (h_yxw' : between y x w') (h_xww' : between x w w') : between y x w := by
  euclid_finish

end Elements.Book1

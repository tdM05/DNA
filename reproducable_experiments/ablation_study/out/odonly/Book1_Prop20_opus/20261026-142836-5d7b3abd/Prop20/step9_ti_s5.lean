import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_20_step9_ti_s5 (x y z w : Point) (XY YZ XZ WZ : Line)
  (h_xXY : x.onLine XY) (h_yXY : y.onLine XY)
  (h_yYZ : y.onLine YZ) (h_zYZ : z.onLine YZ)
  (h_zXZ : z.onLine XZ) (h_xXZ : x.onLine XZ)
  (h_wWZ : w.onLine WZ) (h_zWZ : z.onLine WZ)
  (h_XY_ne_YZ : XY ≠ YZ) (h_YZ_ne_XZ : YZ ≠ XZ) (h_XZ_ne_XY : XZ ≠ XY)
  (s1 : between y x w) (s4 : ∠ x:w:z = ∠ x:z:w) : ∠ y:z:w > ∠ x:w:z := by
  euclid_finish

end Elements.Book1

import SystemE
import Book1.Prop19.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_20_step9_ti_s6 (x y z w : Point) (XY YZ XZ WZ : Line)
  (h_xXY : x.onLine XY) (h_yXY : y.onLine XY)
  (h_yYZ : y.onLine YZ) (h_zYZ : z.onLine YZ)
  (h_zWZ : z.onLine WZ) (h_wWZ : w.onLine WZ)
  (h_zXZ : z.onLine XZ) (h_xXZ : x.onLine XZ)
  (h_XY_ne_YZ : XY ≠ YZ) (h_YZ_ne_XZ : YZ ≠ XZ) (h_XZ_ne_XY : XZ ≠ XY)
  (s1 : between y x w) (s5 : ∠ y:z:w > ∠ x:w:z) : |(w─y)| > |(y─z)| := by
  have htri : formTriangle y z w YZ WZ XY := by euclid_finish
  euclid_apply (proposition_19 y z w YZ WZ XY)
  euclid_finish

end Elements.Book1

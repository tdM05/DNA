import SystemE
import Book1.Prop05.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_20_step9_ti_s4 (x z w w' : Point) (XY XZ WZ : Line)
  (h_xXY : x.onLine XY) (h_w'XY : w'.onLine XY) (h_xww' : between x w w')
  (h_zXZ : z.onLine XZ) (h_xXZ : x.onLine XZ) (h_XZ_ne_XY : XZ ≠ XY)
  (h_wWZ : w.onLine WZ) (h_zWZ : z.onLine WZ)
  (h_xw_eq_xz : |(x─w)| = |(x─z)|) : ∠ x:w:z = ∠ x:z:w := by
  have htri : formTriangle x w z XY WZ XZ := by euclid_finish
  euclid_apply (extend_point XZ x z) as e
  euclid_apply (proposition_5 x w z w' e XY WZ XZ)
  euclid_finish

end Elements.Book1

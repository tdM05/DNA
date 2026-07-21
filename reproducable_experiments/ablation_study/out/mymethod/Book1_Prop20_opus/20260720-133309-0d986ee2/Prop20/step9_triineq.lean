import SystemE
import Book1.Prop05.Main
import Book1.Prop19.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

-- Generic "two sides > the third" for a triangle x y z (apex x): |xy| + |xz| > |yz|.
-- Mirrors the Prop20 construction: extend Y-X beyond X to W with XW = XZ, join WZ,
-- then ∠YZW > ∠YWZ gives WY > YZ (Prop.1.19), and WY = XY + XW = XY + XZ.
theorem helper_1_20_step9_triineq (x y z : Point) (XY YZ XZ : Line)
    (htri : formTriangle x y z XY YZ XZ)
    : |(x─y)| + |(x─z)| > |(y─z)| := by
  euclid_apply (extend_point_longer XY y x (z─x)) as w'
  euclid_apply (proposition_3 x w' x z XY XZ) as w
  euclid_apply (line_from_points w z) as WZ
  euclid_apply (extend_point XZ x z) as ez
  have h_yxw : between y x w := by euclid_finish
  have h_iso : ∠ x:w:z = ∠ x:z:w := by
    have htri2 : formTriangle x w z XY WZ XZ := by euclid_finish
    euclid_apply (proposition_5 x w z w' ez XY WZ XZ)
    euclid_finish
  have h_gt : ∠ y:z:w > ∠ y:w:z := by
    euclid_apply (pasch_2 y x w YZ)
    euclid_apply (pasch_2 w x y WZ)
    euclid_apply (sum_angles_onlyif z y w x YZ WZ)
    euclid_finish
  have h_big : |(y─w)| > |(y─z)| := by
    have htri3 : formTriangle y z w YZ WZ XY := by euclid_finish
    euclid_apply (proposition_19 y z w YZ WZ XY)
    euclid_finish
  euclid_finish

end Elements.Book1

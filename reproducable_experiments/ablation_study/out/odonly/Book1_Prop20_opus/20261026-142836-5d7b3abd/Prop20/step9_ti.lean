import SystemE
import Book1.Prop03.Main
import Book1.Prop20.step9_ti_s1
import Book1.Prop20.step9_ti_s4
import Book1.Prop20.step9_ti_s5
import Book1.Prop20.step9_ti_s6
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_20_step9_ti (x y z : Point) (XY YZ XZ : Line)
  (h : formTriangle x y z XY YZ XZ) : |(y─x)| + |(x─z)| > |(y─z)| := by
  euclid_apply (extend_point_longer XY y x (z─x)) as w'
  euclid_apply (proposition_3 x w' x z XY XZ) as w
  euclid_apply (line_from_points w z) as WZ
  have step9_ti_s1 : between y x w := by euclid_apply (helper_1_20_step9_ti_s1 x y w w' XY (by euclid_assumption "" (show x.onLine XY; assumption)) (by euclid_assumption "" (show y.onLine XY; assumption)) (by euclid_assumption "" (show w'.onLine XY; assumption)) (by euclid_assumption "" (show between y x w'; assumption)) (by euclid_assumption "" (show between x w w'; assumption)))
  have step9_ti_s4 : ∠ x:w:z = ∠ x:z:w := by euclid_apply (helper_1_20_step9_ti_s4 x z w w' XY XZ WZ (by euclid_assumption "" (show x.onLine XY; assumption)) (by euclid_assumption "" (show w'.onLine XY; assumption)) (by euclid_assumption "" (show between x w w'; assumption)) (by euclid_assumption "" (show z.onLine XZ; assumption)) (by euclid_assumption "" (show x.onLine XZ; assumption)) (by euclid_assumption "" (show XZ ≠ XY; assumption)) (by euclid_assumption "" (show w.onLine WZ; assumption)) (by euclid_assumption "" (show z.onLine WZ; assumption)) (by euclid_assumption "" (show |(x─w)| = |(x─z)|; assumption)))
  have step9_ti_s5 : ∠ y:z:w > ∠ x:w:z := by euclid_apply (helper_1_20_step9_ti_s5 x y z w XY YZ XZ WZ (by euclid_assumption "" (show x.onLine XY; assumption)) (by euclid_assumption "" (show y.onLine XY; assumption)) (by euclid_assumption "" (show y.onLine YZ; assumption)) (by euclid_assumption "" (show z.onLine YZ; assumption)) (by euclid_assumption "" (show z.onLine XZ; assumption)) (by euclid_assumption "" (show x.onLine XZ; assumption)) (by euclid_assumption "" (show w.onLine WZ; assumption)) (by euclid_assumption "" (show z.onLine WZ; assumption)) (by euclid_assumption "" (show XY ≠ YZ; assumption)) (by euclid_assumption "" (show YZ ≠ XZ; assumption)) (by euclid_assumption "" (show XZ ≠ XY; assumption)) (by euclid_assumption "" (show between y x w; assumption)) (by euclid_assumption "" (show ∠ x:w:z = ∠ x:z:w; assumption)))
  have step9_ti_s6 : |(w─y)| > |(y─z)| := by euclid_apply (helper_1_20_step9_ti_s6 x y z w XY YZ XZ WZ (by euclid_assumption "" (show x.onLine XY; assumption)) (by euclid_assumption "" (show y.onLine XY; assumption)) (by euclid_assumption "" (show y.onLine YZ; assumption)) (by euclid_assumption "" (show z.onLine YZ; assumption)) (by euclid_assumption "" (show z.onLine WZ; assumption)) (by euclid_assumption "" (show w.onLine WZ; assumption)) (by euclid_assumption "" (show z.onLine XZ; assumption)) (by euclid_assumption "" (show x.onLine XZ; assumption)) (by euclid_assumption "" (show XY ≠ YZ; assumption)) (by euclid_assumption "" (show YZ ≠ XZ; assumption)) (by euclid_assumption "" (show XZ ≠ XY; assumption)) (by euclid_assumption "" (show between y x w; assumption)) (by euclid_assumption "" (show ∠ y:z:w > ∠ x:w:z; assumption)))
  euclid_finish

end Elements.Book1

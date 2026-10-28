import SystemE
import Book1.Prop11.Main
import Book1.Prop08.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3
open Elements.Book1

theorem helper_3_25_step2 (a b c d : Point) (AC DB : Line)
    (hAa : a.onLine AC) (hAc : c.onLine AC) (hac : a ≠ c) (hbAC : ¬b.onLine AC)
    (hab_cb : |(a─b)| = |(c─b)|) (hadc : between a d c) (hstep1 : |(a─d)| = |(d─c)|)
    (hdDB : d.onLine DB) (hbDB : b.onLine DB) : ∠ a:d:b = ∟ := by
  -- Honor the [Prop.~1.11] citation: a perpendicular exists at d on AC.
  euclid_apply (proposition_11 a c d AC) as f
  -- SSS: triangles ADB and CDB are congruent, so ∠ADB = ∠CDB.
  euclid_apply (line_from_points a b) as AB
  euclid_apply (line_from_points c b) as CB
  euclid_apply (proposition_8 d a b d c b AC AB DB AC CB DB)
  -- Two equal adjacent angles on the straight line AC ⟹ right angle.
  euclid_apply (perpendicular_if a c d b AC)
  euclid_finish

end Elements.Book3

import SystemE
import Book1Variants.Prop05
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
theorem helper_2_4_step6 (a b d : Point) (AB AD BD : Line)
    (ha_ab : a.onLine AB) (hb_ab : b.onLine AB) (hab : a ≠ b)
    (ha_ad : a.onLine AD) (hd_ad : d.onLine AD)
    (hb_bd : b.onLine BD) (hd_bd : d.onLine BD)
    (hang : ∠ b:a:d = ∟)
    (hassump1 : |(a─d)| = |(a─b)|)   -- "the side $BA$ is also equal to $AD$"
    : ∠ a:d:b = ∠ a:b:d := by
  have had : a ≠ d := by euclid_finish
  have hd_off_ab : ¬(d.onLine AB) := offLine_of_right_angle a b d AB ha_ab hb_ab hab had hang
  have hb_off_ad : ¬(b.onLine AD) := offLine_of_right_angle a d b AD ha_ad hd_ad had hab (by euclid_finish)
  have ha_off_bd : ¬(a.onLine BD) := offLine_of_two_points a b d AB BD ha_ab hb_ab hab hb_bd hd_bd hd_off_ab
  euclid_apply (Elements.Book1.proposition_5' a d b AD BD AB)
  euclid_finish

end Elements.Book2

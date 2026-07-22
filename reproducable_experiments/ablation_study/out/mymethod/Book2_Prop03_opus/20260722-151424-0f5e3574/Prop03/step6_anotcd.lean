import SystemE
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements

theorem helper_2_3_step6_anotcd (a b c d : Point) (AB CD : Line)
    (ha_AB : a.onLine AB) (hb_AB : b.onLine AB) (hc_AB : c.onLine AB)
    (hc_CD : c.onLine CD) (hd_CD : d.onLine CD)
    (hacb : between a c b) (hbcd : ∠ b:c:d = ∟)
    (hcd_eq : |(c─d)| = |(c─b)|) :
    ¬(a.onLine CD) := by
  have hcb_ne : c ≠ b := by euclid_finish
  have hcd_ne : c ≠ d := by euclid_finish
  have hac_ne : a ≠ c := by euclid_finish
  have hd_notAB : ¬(d.onLine AB) :=
    offLine_of_right_angle c b d AB hc_AB hb_AB hcb_ne hcd_ne hbcd
  exact offLine_of_two_points a c d AB CD ha_AB hc_AB hac_ne hc_CD hd_CD hd_notAB

end Elements.Book2

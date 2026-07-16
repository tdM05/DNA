import SystemE
import Helpers.OffLine
import Helpers.SameSide
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
theorem helper_2_4_step25_adeb (a b d e : Point) (AB AD BE DE : Line)
    (ha_ab : a.onLine AB) (hb_ab : b.onLine AB) (hab : a ≠ b)
    (ha_ad : a.onLine AD) (hd_ad : d.onLine AD)
    (hb_be : b.onLine BE) (he_be : e.onLine BE)
    (hd_de : d.onLine DE) (he_de : e.onLine DE)
    (hang : ∠ b:a:d = ∟) (had_len : |(a─d)| = |(a─b)|) (hde_len : |(d─e)| = |(a─b)|)
    (hAD_BE : ¬(AD.intersectsLine BE)) (hDE_AB : ¬(DE.intersectsLine AB))
    : formParallelogram b e a d BE AD AB DE := by
  have had : a ≠ d := by euclid_finish
  have hd_off_ab : ¬(d.onLine AB) := offLine_of_right_angle a b d AB ha_ab hb_ab hab had hang
  have hAB_ne_DE : AB ≠ DE := (line_ne_of_offLine d DE AB hd_de hd_off_ab).symm
  have hAB_DE : ¬(AB.intersectsLine DE) := fun x => hDE_AB (intersection_symm AB DE x)
  have hba_ss : b.sameSide a DE := sameSide_of_parallel_both b a AB DE hb_ab ha_ab hAB_ne_DE hAB_DE
  have hBE_AD : ¬(BE.intersectsLine AD) := fun x => hAD_BE (intersection_symm BE AD x)
  euclid_finish

end Elements.Book2

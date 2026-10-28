import SystemE
import Helpers.Pasch
import Helpers.OffLine
import Helpers.SameSide
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
theorem helper_2_3_step2_efopp
    (a b c d e f : Point) (AB CD BE AF : Line)
    (hc_CD : c.onLine CD) (hc_AB : c.onLine AB) (ha_AB : a.onLine AB) (hb_AB : b.onLine AB)
    (hbet_acb : between a c b) (hang_bcd : ∠ b:c:d = ∟) (hcd_len : |(c─d)| = |(c─b)|)
    (hd_CD : d.onLine CD)
    (ha_AF : a.onLine AF) (hf_AF : f.onLine AF) (hpar_AFCD : ¬AF.intersectsLine CD)
    (he_BE : e.onLine BE) (hb_BE : b.onLine BE) (hpar_CDBE : ¬CD.intersectsLine BE)
    (hdsc_BE : d.sameSide c BE) :
    ¬(e.sameSide f CD) := by
  -- basic distinctness
  have hcb : c ≠ b := by euclid_finish
  have hac : a ≠ c := by euclid_finish
  have hcd_ne : c ≠ d := by euclid_finish
  -- opposite sides a,b across CD (c is between them, on CD)
  have hab : ¬(a.sameSide b CD) := not_sameSide_of_between a c b CD hc_CD hbet_acb
  -- off-line facts
  have hd_offAB : ¬d.onLine AB := offLine_of_right_angle c b d AB hc_AB hb_AB hcb hcd_ne hang_bcd
  have ha_offCD : ¬a.onLine CD := offLine_of_two_points a c d AB CD ha_AB hc_AB hac hc_CD hd_CD hd_offAB
  have hAFCD : AF ≠ CD := line_ne_of_offLine a AF CD ha_AF ha_offCD
  have hc_offBE : ¬c.onLine BE := by euclid_finish
  -- f and a on AF (parallel to CD) ⟹ same side of CD
  have hfa : f.sameSide a CD := sameSide_of_parallel_both f a AF CD hf_AF ha_AF hAFCD hpar_AFCD
  -- e and b on BE (parallel to CD) ⟹ same side of CD, witness c on CD off BE
  have heb : e.sameSide b CD := sameSide_of_parallel e b c BE CD he_BE hb_BE hc_CD hc_offBE hpar_CDBE
  euclid_finish

end Elements.Book2

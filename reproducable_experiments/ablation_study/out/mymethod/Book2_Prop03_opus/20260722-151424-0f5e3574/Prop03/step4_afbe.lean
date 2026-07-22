import SystemE
import Helpers.Parallel
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements

theorem helper_2_3_step4_afbe (a b c d e : Point) (AB CD BE AF : Line)
    (ha_AF : a.onLine AF) (ha_AB : a.onLine AB) (hb_AB : b.onLine AB) (hc_AB : c.onLine AB)
    (hc_CD : c.onLine CD) (hd_CD : d.onLine CD) (hb_BE : b.onLine BE) (he_BE : e.onLine BE)
    (hacb : between a c b) (hbcd : ∠ b:c:d = ∟) (hcbe : ∠ c:b:e = ∟)
    (h_dc_be : d.sameSide c BE)
    (hAFCD : ¬(AF.intersectsLine CD)) (hCDBE : ¬(CD.intersectsLine BE)) :
    ¬(AF.intersectsLine BE) := by
  have ha_notCD : ¬(a.onLine CD) := by euclid_finish
  have ha_notBE : ¬(a.onLine BE) := by euclid_finish
  have hc_notBE : ¬(c.onLine BE) := by euclid_finish
  have hne_AFCD : AF ≠ CD := line_ne_of_offLine a AF CD ha_AF ha_notCD
  have hne_CDBE : CD ≠ BE := line_ne_of_offLine c CD BE hc_CD hc_notBE
  have hne_AFBE : AF ≠ BE := line_ne_of_offLine a AF BE ha_AF ha_notBE
  exact not_intersects_trans AF CD BE hAFCD hCDBE hne_AFCD hne_CDBE hne_AFBE

end Elements.Book2

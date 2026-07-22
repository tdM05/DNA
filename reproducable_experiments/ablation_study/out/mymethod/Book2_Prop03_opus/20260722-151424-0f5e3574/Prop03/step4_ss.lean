import SystemE
import Helpers.SameSide
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements

theorem helper_2_3_step4_ss (a b c d e f : Point) (AB CD BE AF : Line)
    (ha_AF : a.onLine AF) (hf_AF : f.onLine AF) (ha_AB : a.onLine AB)
    (hb_AB : b.onLine AB) (hc_AB : c.onLine AB) (hc_CD : c.onLine CD)
    (hd_CD : d.onLine CD) (hb_BE : b.onLine BE) (he_BE : e.onLine BE)
    (hacb : between a c b) (hbcd : ∠ b:c:d = ∟) (hcbe : ∠ c:b:e = ∟)
    (h_dc_be : d.sameSide c BE)
    (hAFBE : ¬(AF.intersectsLine BE)) :
    a.sameSide f BE := by
  have ha_notBE : ¬(a.onLine BE) := by euclid_finish
  have hne_AFBE : AF ≠ BE := line_ne_of_offLine a AF BE ha_AF ha_notBE
  exact sameSide_of_parallel_both a f AF BE ha_AF hf_AF hne_AFBE hAFBE

end Elements.Book2

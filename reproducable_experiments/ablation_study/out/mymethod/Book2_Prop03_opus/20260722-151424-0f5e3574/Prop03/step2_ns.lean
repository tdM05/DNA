import SystemE
import Helpers.SameSide
import Helpers.Pasch
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements

theorem helper_2_3_step2_ns (a b c d e f : Point) (AB CD BE AF : Line)
    (he_BE : e.onLine BE) (hb_BE : b.onLine BE) (ha_AF : a.onLine AF) (hf_AF : f.onLine AF)
    (hc_CD : c.onLine CD) (hc_AB : c.onLine AB) (ha_AB : a.onLine AB) (hb_AB : b.onLine AB)
    (hacb : between a c b) (hbcd : ∠ b:c:d = ∟) (h_dc_be : d.sameSide c BE)
    (hCDBE : ¬CD.intersectsLine BE) (hAFCD : ¬AF.intersectsLine CD) :
    ¬(e.sameSide f CD) := by
  have hc_notBE : ¬(c.onLine BE) := by euclid_finish
  have ha_notCD : ¬(a.onLine CD) := by euclid_finish
  have hbe : b.sameSide e CD := sameSide_of_parallel b e c BE CD hb_BE he_BE hc_CD hc_notBE hCDBE
  have haf : a.sameSide f CD := sameSide_of_parallel' a f a AF CD ha_AF hf_AF ha_AF ha_notCD hAFCD
  have hab : ¬(a.sameSide b CD) := not_sameSide_of_between a c b CD hc_CD hacb
  euclid_finish

end Elements.Book2

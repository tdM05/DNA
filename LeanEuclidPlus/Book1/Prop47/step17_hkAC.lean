import SystemE
import Helpers.SameSide
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_47_step17_hkAC
    (h k : Point) (HK AC : Line)
    (hhHK : h.onLine HK) (hkHK : k.onLine HK)
    (hhoffAC : ¬h.onLine AC) (hHKAC : ¬HK.intersectsLine AC) :
    h.sameSide k AC := by
  euclid_apply (Elements.sameSide_of_parallel' h k h HK AC hhHK hkHK hhHK hhoffAC hHKAC)

end Elements.Book1

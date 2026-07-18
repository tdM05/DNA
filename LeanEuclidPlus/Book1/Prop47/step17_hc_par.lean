import SystemE
import Helpers.SameSide
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_47_step17_hc_par
    (a b c h k : Point) (AB CK HK AC : Line)
    (hbAB : b.onLine AB) (haAB : a.onLine AB)
    (hkCK : k.onLine CK) (hcCK : c.onLine CK)
    (hhHK : h.onLine HK) (hkHK : k.onLine HK)
    (haAC : a.onLine AC) (hcAC : c.onLine AC)
    (hbah : between b a h) (hhoffAC : ¬h.onLine AC)
    (hABCK : ¬AB.intersectsLine CK) (hHKAC : ¬HK.intersectsLine AC)
    (hac : a ≠ c) :
    formParallelogram h a k c AB CK HK AC := by
  have hhAB : h.onLine AB := by euclid_finish
  have hhkAC : h.sameSide k AC := by
    euclid_apply (Elements.sameSide_of_parallel' h k h HK AC hhHK hkHK hhHK hhoffAC hHKAC)
  euclid_finish

end Elements.Book1

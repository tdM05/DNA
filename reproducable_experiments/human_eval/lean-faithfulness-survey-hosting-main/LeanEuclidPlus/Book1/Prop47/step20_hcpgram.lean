import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_47_s20_x2
    (a c h k : Point) (AC HK AH CK : Line)
    (ha_AC : a.onLine AC) (hc_AC : c.onLine AC)
    (hh_HK : h.onLine HK) (hk_HK : k.onLine HK)
    (ha_AH : a.onLine AH) (hh_AH : h.onLine AH)
    (hc_CK : c.onLine CK) (hk_CK : k.onLine CK) (hkc : k ≠ c)
    (h_h_same_a_CK : h.sameSide a CK)
    (h_nHKAC : ¬HK.intersectsLine AC) (h_nAHCK : ¬AH.intersectsLine CK) :
    formParallelogram a c h k AC HK AH CK := by
  euclid_finish

end Elements.Book1

import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_47_step20_hc_par
    (a c h k : Point) (HK AC AH CK : Line)
    (hhHK : h.onLine HK) (hkHK : k.onLine HK)
    (haAC : a.onLine AC) (hcAC : c.onLine AC)
    (hhAH : h.onLine AH) (haAH : a.onLine AH)
    (hkCK : k.onLine CK) (hcCK : c.onLine CK) (hkc : k ≠ c)
    (hhaCK : h.sameSide a CK)
    (hHKAC : ¬HK.intersectsLine AC) (hAHCK : ¬AH.intersectsLine CK) :
    formParallelogram h k a c HK AC AH CK := by
  euclid_finish

end Elements.Book1

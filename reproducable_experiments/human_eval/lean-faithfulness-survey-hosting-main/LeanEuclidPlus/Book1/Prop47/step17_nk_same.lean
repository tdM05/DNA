import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_47_s17_x8
    (b h k : Point) (AC HK : Line)
    (hh_HK : h.onLine HK) (hk_HK : k.onLine HK)
    (h_nHKAC : ¬HK.intersectsLine AC)
    (hh_nAC : ¬h.onLine AC) (hk_nAC : ¬k.onLine AC) (hb_nAC : ¬b.onLine AC)
    (h_nh_same_b_AC : ¬h.sameSide b AC) :
    ¬k.sameSide b AC := by
  have hkh : k.sameSide h AC := by
    by_contra hcon
    euclid_apply (intersection_lines_opposing k h AC HK)
    euclid_finish
  euclid_finish

end Elements.Book1

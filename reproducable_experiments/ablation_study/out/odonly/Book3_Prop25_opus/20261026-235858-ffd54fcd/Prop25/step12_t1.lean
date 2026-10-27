import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_step12_t1 (a b c d e : Point) (AC AG DB : Line)
    (ha_AC : a.onLine AC) (hc_AC : c.onLine AC) (hadc : between a d c)
    (hb_off : ¬b.onLine AC) (hb_DB : b.onLine DB)
    (hd_DB : d.onLine DB) (he_DB : e.onLine DB)
    (ha_AG : a.onLine AG) (he_AG : e.onLine AG)
    (he_off : ¬ e.onLine AC) :
    formTriangle d a e AC AG DB := by
  euclid_finish

end Elements.Book3

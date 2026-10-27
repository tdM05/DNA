import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_step12_t2 (a b c d e : Point) (AC EC DB : Line)
    (ha_AC : a.onLine AC) (hc_AC : c.onLine AC) (hadc : between a d c)
    (hb_off : ¬b.onLine AC) (hb_DB : b.onLine DB)
    (hd_DB : d.onLine DB) (he_DB : e.onLine DB)
    (hc_EC : c.onLine EC) (he_EC : e.onLine EC)
    (he_off : ¬ e.onLine AC) :
    formTriangle d c e AC EC DB := by
  euclid_finish

end Elements.Book3

import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

-- mirrors step6_hdab: d on PQ (from between p d d0, p and d0 on PQ)
theorem helper_1_20_step9_triineq_side_hdpq (p d d0 : Point) (PQ : Line)
    (hpPQ : p.onLine PQ) (hd0PQ : d0.onLine PQ) (hpdd0 : between p d d0)
    : d.onLine PQ := by
  euclid_apply (between_same_line_in p d d0 PQ)
  euclid_finish

end Elements.Book1

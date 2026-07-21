import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

-- mirrors step1: between q p d from between q p d0 and between p d d0
theorem helper_1_20_step9_triineq_qpd (p q d d0 : Point) (PQ : Line)
    (hpPQ : p.onLine PQ) (hqPQ : q.onLine PQ) (hd0PQ : d0.onLine PQ) (hpq : p ≠ q)
    (h1 : between q p d0) (h2 : between p d d0) : between q p d := by
  euclid_finish

end Elements.Book1

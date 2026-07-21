import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

-- mirrors step6_hbdc: q off DR (q,d on PQ; d,r on DR; r off PQ; between q p d gives q≠d)
theorem helper_1_20_step9_triineq_side_hqdr (p q r d : Point) (PQ DR : Line)
    (hqPQ : q.onLine PQ) (hdPQ : d.onLine PQ) (hqpd : between q p d)
    (hrDR : r.onLine DR) (hdDR : d.onLine DR) (hrPQ : ¬ r.onLine PQ)
    : ¬ q.onLine DR := by
  euclid_finish

end Elements.Book1

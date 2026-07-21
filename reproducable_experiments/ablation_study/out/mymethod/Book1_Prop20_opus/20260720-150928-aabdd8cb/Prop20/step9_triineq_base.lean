import SystemE
import Book1.Prop05.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

-- mirrors step4: isosceles base angles of triangle p-d-r (|pd|=|pr|) via Prop.1.5
theorem helper_1_20_step9_triineq_base (p r d d0 : Point) (PQ PR DR : Line)
    (hpPQ : p.onLine PQ) (hd0PQ : d0.onLine PQ) (hpdd0 : between p d d0)
    (hdDR : d.onLine DR) (hrDR : r.onLine DR)
    (hpPR : p.onLine PR) (hrPR : r.onLine PR) (hPRPQ : PR ≠ PQ)
    (hpd : |(p─d)| = |(p─r)|)
    : ∠ p:d:r = ∠ p:r:d := by
  euclid_apply (extend_point PR p r) as e
  euclid_apply (proposition_5 p d r d0 e PQ DR PR)
  euclid_finish

end Elements.Book1

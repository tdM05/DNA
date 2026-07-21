import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

-- mirrors step6_hcab: r off PQ (r on PR, p on PQ∩PR, PR≠PQ, triangle distinctness)
theorem helper_1_20_step9_triineq_side_hrpq (p q r : Point) (PQ QR PR : Line)
    (hpPQ : p.onLine PQ) (hqPQ : q.onLine PQ) (hpq : p ≠ q)
    (hqQR : q.onLine QR) (hrQR : r.onLine QR)
    (hrPR : r.onLine PR) (hpPR : p.onLine PR)
    (hPQQR : PQ ≠ QR) (hQRPR : QR ≠ PR) (hPRPQ : PR ≠ PQ)
    : ¬ r.onLine PQ := by
  euclid_finish

end Elements.Book1

import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

-- mirrors step5: ∠ q:r:d > ∠ p:d:r  (ray rp interior to ∠ q:r:d, plus base-angle equality)
theorem helper_1_20_step9_triineq_gt1 (p q r d d0 : Point) (PQ QR PR DR : Line)
    (hpPQ : p.onLine PQ) (hd0PQ : d0.onLine PQ) (hpdd0 : between p d d0)
    (hqQR : q.onLine QR) (hrQR : r.onLine QR)
    (hrPR : r.onLine PR) (hpPR : p.onLine PR)
    (hPQQR : PQ ≠ QR) (hQRPR : QR ≠ PR) (hPRPQ : PR ≠ PQ)
    (hdDR : d.onLine DR) (hrDR : r.onLine DR)
    (hqpd : between q p d)
    (hbase : ∠ p:d:r = ∠ p:r:d)
    : ∠ q:r:d > ∠ p:d:r := by
  have hpDR : ¬ p.onLine DR := by euclid_finish
  have hpQR : ¬ p.onLine QR := by euclid_finish
  euclid_apply (pasch_2 d p q DR)
  euclid_apply (pasch_2 q p d QR)
  euclid_finish

end Elements.Book1

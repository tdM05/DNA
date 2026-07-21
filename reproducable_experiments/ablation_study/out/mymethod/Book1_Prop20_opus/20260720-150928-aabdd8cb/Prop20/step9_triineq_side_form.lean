import SystemE
import Book1.Prop20.step9_triineq_side_hdpq
import Book1.Prop20.step9_triineq_side_hrpq
import Book1.Prop20.step9_triineq_side_hqdr
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

-- mirrors step6_form: formTriangle q r d QR DR PQ (betweenness kept out of the assembly)
theorem helper_1_20_step9_triineq_side_form (p q r d d0 : Point) (PQ QR PR DR : Line)
    (hpPQ : p.onLine PQ) (hqPQ : q.onLine PQ) (hpq : p ≠ q) (hd0PQ : d0.onLine PQ)
    (hpdd0 : between p d d0) (hqpd : between q p d)
    (hqQR : q.onLine QR) (hrQR : r.onLine QR)
    (hrDR : r.onLine DR) (hdDR : d.onLine DR)
    (hrPR : r.onLine PR) (hpPR : p.onLine PR)
    (hPQQR : PQ ≠ QR) (hQRPR : QR ≠ PR) (hPRPQ : PR ≠ PQ)
    : formTriangle q r d QR DR PQ := by
  have step9_triineq_side_hdpq : d.onLine PQ := by euclid_apply (helper_1_20_step9_triineq_side_hdpq p d d0 PQ (by euclid_assumption "" (show p.onLine PQ; assumption)) (by euclid_assumption "" (show d0.onLine PQ; assumption)) (by euclid_assumption "" (show between p d d0; assumption)))
  have step9_triineq_side_hrpq : ¬ r.onLine PQ := by euclid_apply (helper_1_20_step9_triineq_side_hrpq p q r PQ QR PR (by euclid_assumption "" (show p.onLine PQ; assumption)) (by euclid_assumption "" (show q.onLine PQ; assumption)) (by euclid_assumption "" (show p ≠ q; assumption)) (by euclid_assumption "" (show q.onLine QR; assumption)) (by euclid_assumption "" (show r.onLine QR; assumption)) (by euclid_assumption "" (show r.onLine PR; assumption)) (by euclid_assumption "" (show p.onLine PR; assumption)) (by euclid_assumption "" (show PQ ≠ QR; assumption)) (by euclid_assumption "" (show QR ≠ PR; assumption)) (by euclid_assumption "" (show PR ≠ PQ; assumption)))
  have step9_triineq_side_hqdr : ¬ q.onLine DR := by euclid_apply (helper_1_20_step9_triineq_side_hqdr p q r d PQ DR (by euclid_assumption "" (show q.onLine PQ; assumption)) (by euclid_assumption "" (show d.onLine PQ; assumption)) (by euclid_assumption "" (show between q p d; assumption)) (by euclid_assumption "" (show r.onLine DR; assumption)) (by euclid_assumption "" (show d.onLine DR; assumption)) (by euclid_assumption "" (show ¬ r.onLine PQ; assumption)))
  euclid_finish

end Elements.Book1

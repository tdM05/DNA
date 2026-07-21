import SystemE
import Book1.Prop03.Main
import Book1.Prop20.step9_triineq_qpd
import Book1.Prop20.step9_triineq_base
import Book1.Prop20.step9_triineq_gt1
import Book1.Prop20.step9_triineq_side
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

-- Generic triangle inequality: for triangle p q r (apex p; sides pq on PQ, pr on PR;
-- opposite side qr on QR), the two sides at p sum to more than the opposite side.
-- Mirrors Euclid's construction (steps 1-8 of Prop20) generically; used by step9 and step10.
theorem helper_1_20_step9_triineq (p q r : Point) (PQ QR PR : Line)
    (htri : formTriangle p q r PQ QR PR) : |(q─p)| + |(p─r)| > |(q─r)| := by
  obtain ⟨⟨hpPQ, hqPQ, hpq⟩, hqQR, hrQR, hrPR, hpPR, hPQQR, hQRPR, hPRPQ⟩ := htri
  euclid_apply (extend_point_longer PQ q p (p─r)) as d0
  euclid_apply (proposition_3 p d0 p r PQ PR) as d
  euclid_apply (line_from_points d r) as DR
  have step9_triineq_qpd : between q p d := by euclid_apply (helper_1_20_step9_triineq_qpd p q d d0 PQ (by euclid_assumption "" (show p.onLine PQ; assumption)) (by euclid_assumption "" (show q.onLine PQ; assumption)) (by euclid_assumption "" (show d0.onLine PQ; assumption)) (by euclid_assumption "" (show p ≠ q; assumption)) (by euclid_assumption "" (show between q p d0; assumption)) (by euclid_assumption "" (show between p d d0; assumption)))
  have step9_triineq_base : ∠ p:d:r = ∠ p:r:d := by euclid_apply (helper_1_20_step9_triineq_base p r d d0 PQ PR DR (by euclid_assumption "" (show p.onLine PQ; assumption)) (by euclid_assumption "" (show d0.onLine PQ; assumption)) (by euclid_assumption "" (show between p d d0; assumption)) (by euclid_assumption "" (show d.onLine DR; assumption)) (by euclid_assumption "" (show r.onLine DR; assumption)) (by euclid_assumption "" (show p.onLine PR; assumption)) (by euclid_assumption "" (show r.onLine PR; assumption)) (by euclid_assumption "" (show PR ≠ PQ; assumption)) (by euclid_assumption "" (show |(p─d)| = |(p─r)|; assumption)))
  have step9_triineq_gt1 : ∠ q:r:d > ∠ p:d:r := by euclid_apply (helper_1_20_step9_triineq_gt1 p q r d d0 PQ QR PR DR (by euclid_assumption "" (show p.onLine PQ; assumption)) (by euclid_assumption "" (show d0.onLine PQ; assumption)) (by euclid_assumption "" (show between p d d0; assumption)) (by euclid_assumption "" (show q.onLine QR; assumption)) (by euclid_assumption "" (show r.onLine QR; assumption)) (by euclid_assumption "" (show r.onLine PR; assumption)) (by euclid_assumption "" (show p.onLine PR; assumption)) (by euclid_assumption "" (show PQ ≠ QR; assumption)) (by euclid_assumption "" (show QR ≠ PR; assumption)) (by euclid_assumption "" (show PR ≠ PQ; assumption)) (by euclid_assumption "" (show d.onLine DR; assumption)) (by euclid_assumption "" (show r.onLine DR; assumption)) (by euclid_assumption "" (show between q p d; assumption)) (by euclid_assumption "" (show ∠ p:d:r = ∠ p:r:d; assumption)))
  have hqrd_gt : ∠ q:r:d > ∠ q:d:r := by euclid_finish
  have step9_triineq_side : |(d─q)| > |(q─r)| := by euclid_apply (helper_1_20_step9_triineq_side p q r d d0 PQ QR PR DR (by euclid_assumption "" (show p.onLine PQ; assumption)) (by euclid_assumption "" (show q.onLine PQ; assumption)) (by euclid_assumption "" (show p ≠ q; assumption)) (by euclid_assumption "" (show d0.onLine PQ; assumption)) (by euclid_assumption "" (show between p d d0; assumption)) (by euclid_assumption "" (show between q p d; assumption)) (by euclid_assumption "" (show q.onLine QR; assumption)) (by euclid_assumption "" (show r.onLine QR; assumption)) (by euclid_assumption "" (show r.onLine DR; assumption)) (by euclid_assumption "" (show d.onLine DR; assumption)) (by euclid_assumption "" (show r.onLine PR; assumption)) (by euclid_assumption "" (show p.onLine PR; assumption)) (by euclid_assumption "" (show PQ ≠ QR; assumption)) (by euclid_assumption "" (show QR ≠ PR; assumption)) (by euclid_assumption "" (show PR ≠ PQ; assumption)) (by euclid_assumption "" (show ∠ q:r:d > ∠ q:d:r; assumption)))
  euclid_finish

end Elements.Book1

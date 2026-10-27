import SystemE
import Book1.Prop03.Main
import Book1.Prop20.step9_ts1
import Book1.Prop20.step9_ts4
import Book1.Prop20.step9_ts5
import Book1.Prop20.step9_ts6
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

-- Generic triangle-inequality helper: in triangle p q r, the two sides meeting at
-- vertex q sum to more than the opposite side p─r.  (Euclid's Prop.~20 argument,
-- applied generically; reused by step9 and step10 via @args.)
theorem helper_1_20_step9_triineq
    (p q r : Point)
    (PQ QR PR : Line)
    (hp_PQ : p.onLine PQ)
    (hq_PQ : q.onLine PQ)
    (hpq : p ≠ q)
    (hq_QR : q.onLine QR)
    (hr_QR : r.onLine QR)
    (hr_PR : r.onLine PR)
    (hp_PR : p.onLine PR)
    (hPQQR : PQ ≠ QR)
    (hQRPR : QR ≠ PR)
    (hPRPQ : PR ≠ PQ)
    : |(p─q)| + |(q─r)| > |(p─r)| := by
  euclid_apply (extend_point_longer PQ p q (q─r)) as s_ext
  euclid_apply (proposition_3 q s_ext q r PQ QR) as s
  euclid_apply (line_from_points s r) as SR
  have step9_ts1 : between p q s := by euclid_apply (helper_1_20_step9_ts1 p q s s_ext PQ (by euclid_assumption "" (show p.onLine PQ; assumption)) (by euclid_assumption "" (show q.onLine PQ; assumption)) (by euclid_assumption "" (show s_ext.onLine PQ; assumption)) (by euclid_assumption "" (show between p q s_ext; assumption)) (by euclid_assumption "" (show between q s s_ext; assumption)))
  have step9_ts4 : ∠ q:s:r = ∠ q:r:s := by euclid_apply (helper_1_20_step9_ts4 p q r s s_ext PQ QR PR SR (by euclid_assumption "" (show p.onLine PQ; assumption)) (by euclid_assumption "" (show q.onLine PQ; assumption)) (by euclid_assumption "" (show p ≠ q; assumption)) (by euclid_assumption "" (show q.onLine QR; assumption)) (by euclid_assumption "" (show r.onLine QR; assumption)) (by euclid_assumption "" (show r.onLine PR; assumption)) (by euclid_assumption "" (show p.onLine PR; assumption)) (by euclid_assumption "" (show PQ ≠ QR; assumption)) (by euclid_assumption "" (show QR ≠ PR; assumption)) (by euclid_assumption "" (show PR ≠ PQ; assumption)) (by euclid_assumption "" (show s_ext.onLine PQ; assumption)) (by euclid_assumption "" (show between q s s_ext; assumption)) (by euclid_assumption "" (show s.onLine SR; assumption)) (by euclid_assumption "" (show r.onLine SR; assumption)) (by euclid_assumption "" (show |(q─s)| = |(q─r)|; assumption)))
  have step9_ts5 : ∠ p:r:s > ∠ q:s:r := by euclid_apply (helper_1_20_step9_ts5 p q r s s_ext PQ QR PR SR (by euclid_assumption "" (show p.onLine PQ; assumption)) (by euclid_assumption "" (show q.onLine PQ; assumption)) (by euclid_assumption "" (show p ≠ q; assumption)) (by euclid_assumption "" (show q.onLine QR; assumption)) (by euclid_assumption "" (show r.onLine QR; assumption)) (by euclid_assumption "" (show r.onLine PR; assumption)) (by euclid_assumption "" (show p.onLine PR; assumption)) (by euclid_assumption "" (show PQ ≠ QR; assumption)) (by euclid_assumption "" (show QR ≠ PR; assumption)) (by euclid_assumption "" (show PR ≠ PQ; assumption)) (by euclid_assumption "" (show s_ext.onLine PQ; assumption)) (by euclid_assumption "" (show between q s s_ext; assumption)) (by euclid_assumption "" (show between p q s_ext; assumption)) (by euclid_assumption "" (show s.onLine SR; assumption)) (by euclid_assumption "" (show r.onLine SR; assumption)) (by euclid_assumption "" (show between p q s; assumption)) (by euclid_assumption "" (show ∠ q:s:r = ∠ q:r:s; assumption)))
  have step9_ts6 : |(p─s)| > |(p─r)| := by euclid_apply (helper_1_20_step9_ts6 p q r s s_ext PQ QR PR SR (by euclid_assumption "" (show p.onLine PQ; assumption)) (by euclid_assumption "" (show q.onLine PQ; assumption)) (by euclid_assumption "" (show p ≠ q; assumption)) (by euclid_assumption "" (show q.onLine QR; assumption)) (by euclid_assumption "" (show r.onLine QR; assumption)) (by euclid_assumption "" (show r.onLine PR; assumption)) (by euclid_assumption "" (show p.onLine PR; assumption)) (by euclid_assumption "" (show PQ ≠ QR; assumption)) (by euclid_assumption "" (show QR ≠ PR; assumption)) (by euclid_assumption "" (show PR ≠ PQ; assumption)) (by euclid_assumption "" (show s_ext.onLine PQ; assumption)) (by euclid_assumption "" (show between q s s_ext; assumption)) (by euclid_assumption "" (show s.onLine SR; assumption)) (by euclid_assumption "" (show r.onLine SR; assumption)) (by euclid_assumption "" (show between p q s; assumption)) (by euclid_assumption "" (show ∠ p:r:s > ∠ q:s:r; assumption)))
  euclid_finish

end Elements.Book1

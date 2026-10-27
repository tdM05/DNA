import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_20_step9_ts5
    (p q r s s_ext : Point) (PQ QR PR SR : Line)
    (hp_PQ : p.onLine PQ) (hq_PQ : q.onLine PQ) (hpq : p ≠ q)
    (hq_QR : q.onLine QR) (hr_QR : r.onLine QR)
    (hr_PR : r.onLine PR) (hp_PR : p.onLine PR)
    (hPQQR : PQ ≠ QR) (hQRPR : QR ≠ PR) (hPRPQ : PR ≠ PQ)
    (hse_PQ : s_ext.onLine PQ) (h_qsse : between q s s_ext) (h_pqse : between p q s_ext)
    (hs_SR : s.onLine SR) (hr_SR : r.onLine SR)
    (step9_ts1 : between p q s)
    (step9_ts4 : ∠ q:s:r = ∠ q:r:s)
    : ∠ p:r:s > ∠ q:s:r := by
  euclid_apply (sum_angles_onlyif r p s q PR SR)
  euclid_finish

end Elements.Book1

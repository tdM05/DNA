import SystemE
import Book1.Prop05.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_20_step9_ts4
    (p q r s s_ext : Point) (PQ QR PR SR : Line)
    (hp_PQ : p.onLine PQ) (hq_PQ : q.onLine PQ) (hpq : p ≠ q)
    (hq_QR : q.onLine QR) (hr_QR : r.onLine QR)
    (hr_PR : r.onLine PR) (hp_PR : p.onLine PR)
    (hPQQR : PQ ≠ QR) (hQRPR : QR ≠ PR) (hPRPQ : PR ≠ PQ)
    (hse_PQ : s_ext.onLine PQ) (h_qsse : between q s s_ext)
    (hs_SR : s.onLine SR) (hr_SR : r.onLine SR)
    (h_qs : |(q─s)| = |(q─r)|)
    : ∠ q:s:r = ∠ q:r:s := by
  euclid_apply (extend_point QR q r) as e_r
  euclid_apply (proposition_5 q s r s_ext e_r PQ SR QR)
  euclid_finish

end Elements.Book1

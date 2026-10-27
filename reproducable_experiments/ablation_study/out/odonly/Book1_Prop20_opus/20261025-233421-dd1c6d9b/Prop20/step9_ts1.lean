import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_20_step9_ts1
    (p q s s_ext : Point) (PQ : Line)
    (hp_PQ : p.onLine PQ) (hq_PQ : q.onLine PQ) (hse_PQ : s_ext.onLine PQ)
    (h_pqse : between p q s_ext) (h_qsse : between q s s_ext)
    : between p q s := by euclid_finish

end Elements.Book1

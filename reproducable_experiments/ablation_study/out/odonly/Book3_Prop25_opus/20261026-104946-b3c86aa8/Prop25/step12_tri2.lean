import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_step12_tri2 (a c d e : Point) (AC EC DB : Line)
    (hAC_a : a.onLine AC) (hAC_c : c.onLine AC) (hbet : between a d c)
    (hc_EC : c.onLine EC) (he_EC : e.onLine EC)
    (hd_DB : d.onLine DB) (he_DB : e.onLine DB)
    (hcde : ∠ c:d:e = ∟) (hed : e ≠ d) :
    formTriangle d c e AC EC DB := by
  have heoff : ¬ e.onLine AC := by euclid_finish
  euclid_finish

end Elements.Book3

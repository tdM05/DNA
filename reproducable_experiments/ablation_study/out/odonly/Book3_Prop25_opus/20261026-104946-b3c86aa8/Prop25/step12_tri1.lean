import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_step12_tri1 (a c d e : Point) (AC AE DB : Line)
    (hAC_a : a.onLine AC) (hAC_c : c.onLine AC) (hbet : between a d c)
    (ha_AE : a.onLine AE) (he_AE : e.onLine AE)
    (hd_DB : d.onLine DB) (he_DB : e.onLine DB)
    (hade : ∠ a:d:e = ∟) (hed : e ≠ d) :
    formTriangle d a e AC AE DB := by
  have heoff : ¬ e.onLine AC := by euclid_finish
  euclid_finish

end Elements.Book3

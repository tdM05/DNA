import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_step9_assumption1 (a b c d e g : Point) (AC DB AB AG : Line)
    (hAC_a : a.onLine AC) (hAC_c : c.onLine AC)
    (hb_off : ¬b.onLine AC)
    (hbet : between a d c)
    (hd_DB : d.onLine DB) (hb_DB : b.onLine DB) (he_DB : e.onLine DB)
    (hAB_a : a.onLine AB) (hAB_b : b.onLine AB)
    (hgNa : g ≠ a)
    (hg_side : g.onLine AB ∨ g.sameSide d AB)
    (hgab : ∠ g:a:b = ∠ a:b:d)
    (hAG_a : a.onLine AG) (hAG_g : g.onLine AG) (he_AG : e.onLine AG)
    (hstep6 : ∠ b:a:e = ∠ a:b:d ∧ e ≠ a) :
    ∠ a:b:e = ∠ b:a:e := by
  euclid_finish

end Elements.Book3

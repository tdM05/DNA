import SystemE
import Book1.Prop32.Main
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1

theorem helper_3_25_hEb_bae (a b c d e g3 : Point) (AC DB AB AG3 : Line)
    (hAC_a : a.onLine AC) (hAC_c : c.onLine AC)
    (hb_off : ¬b.onLine AC)
    (hbet : between a d c)
    (hd_DB : d.onLine DB) (hb_DB : b.onLine DB) (he_DB : e.onLine DB)
    (hAB_a : a.onLine AB) (hAB_b : b.onLine AB)
    (hadb : ∠ a:d:b = ∟)
    (hgNa : g3 ≠ a)
    (hg_side : g3.onLine AB ∨ g3.sameSide d AB)
    (hgab : ∠ g3:a:b = ∠ a:b:d)
    (hAG_a : a.onLine AG3) (hAG_g : g3.onLine AG3) (he_AG : e.onLine AG3) :
    ∠ b:a:e = ∠ a:b:d := by
  euclid_apply (proposition_32 b a d c AB AC DB)
  euclid_finish

end Elements.Book3

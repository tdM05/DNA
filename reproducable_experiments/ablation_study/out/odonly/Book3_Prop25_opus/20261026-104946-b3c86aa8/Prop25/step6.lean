import SystemE
import Book1.Prop32.Main
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1

theorem helper_3_25_step6 (a b c d e g : Point) (AC DB AB AG : Line)
    (hAC_a : a.onLine AC) (hAC_c : c.onLine AC)
    (hb_off : ¬b.onLine AC)
    (hbet : between a d c)
    (hd_DB : d.onLine DB) (hb_DB : b.onLine DB) (he_DB : e.onLine DB)
    (hAB_a : a.onLine AB) (hAB_b : b.onLine AB)
    (hadb : ∠ a:d:b = ∟)
    (hgt : ∠ a:b:d > ∠ b:a:d)
    (hgNa : g ≠ a)
    (hg_side : g.onLine AB ∨ g.sameSide d AB)
    (hgab : ∠ g:a:b = ∠ a:b:d)
    (hAG_a : a.onLine AG) (hAG_g : g.onLine AG) (he_AG : e.onLine AG) :
    ∠ b:a:e = ∠ a:b:d ∧ e ≠ a := by
  euclid_apply (proposition_32 b a d c AB AC DB)
  euclid_finish

end Elements.Book3

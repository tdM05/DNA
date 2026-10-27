import SystemE
import Book1.Prop32.Main
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1

theorem helper_3_25_hAGDB (a b c d g : Point) (AC DB AB AG : Line)
    (hAC_a : a.onLine AC) (hAC_c : c.onLine AC) (hac : a ≠ c)
    (hb_off : ¬b.onLine AC)
    (hbet : between a d c)
    (hd_DB : d.onLine DB) (hb_DB : b.onLine DB)
    (hAB_a : a.onLine AB) (hAB_b : b.onLine AB)
    (hadb : ∠ a:d:b = ∟)
    (hgNa : g ≠ a)
    (hg_side : g.onLine AB ∨ g.sameSide d AB)
    (hgab : ∠ g:a:b = ∠ a:b:d)
    (hAG_a : a.onLine AG) (hAG_g : g.onLine AG) :
    AG.intersectsLine DB := by
  -- Angle sum in triangle BAD (right-angled at D): ∠BAD + ∠ABD = ∟, so ∠ABD < ∟.
  euclid_apply (proposition_32 b a d c AB AC DB)
  -- Converging lines AG, DB meet: transversal AB, with ∠GAB + ∠ABD = 2·∠ABD < 2∟.
  euclid_finish

end Elements.Book3

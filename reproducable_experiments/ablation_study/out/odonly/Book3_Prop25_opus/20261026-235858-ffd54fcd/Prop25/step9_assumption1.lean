import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_step9_assumption1 (a b c d g e : Point) (AC DB AB AG : Line)
    (ha_AC : a.onLine AC) (hc_AC : c.onLine AC) (hac : a ≠ c)
    (hb_off : ¬b.onLine AC) (hadc : between a d c)
    (hd_DB : d.onLine DB) (hb_DB : b.onLine DB)
    (ha_AB : a.onLine AB) (hb_AB : b.onLine AB) (hab : a ≠ b)
    (hstep2 : ∠ a:d:b = ∟) (hgt : ∠ a:b:d > ∠ b:a:d)
    (hga : g ≠ a) (hgab : ∠ g:a:b = ∠ a:b:d)
    (hg_side : g.onLine AB ∨ g.sameSide d AB)
    (ha_AG : a.onLine AG) (hg_AG : g.onLine AG)
    (he_AG : e.onLine AG) (he_DB : e.onLine DB)
    (hstep6 : ∠ b:a:e = ∠ a:b:d ∧ e ≠ a) :
    ∠ a:b:e = ∠ b:a:e := by
  obtain ⟨hstep6a, hea⟩ := hstep6
  euclid_finish

end Elements.Book3

import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1
open Elements

theorem h_1_44_s8
    (b e f g h : Point) (BG EF GF AH HB : Line)
    (hfGF : f.onLine GF) (hfBG : f.onLine BG)
    (hgGF : g.onLine GF) (hgEF : g.onLine EF)
    (hhGF : h.onLine GF) (hhHB : h.onLine HB)
    (hbHB : b.onLine HB) (hbBG : b.onLine BG)
    (heEF : e.onLine EF)
    (hge : g ≠ e)
    (s3 : between g f h)
    (hBGEF : ¬BG.intersectsLine EF)
    (hAHBG : ¬AH.intersectsLine BG)
    (s6_a1 : ¬AH.intersectsLine EF ∧ GF.intersectsLine AH ∧ GF.intersectsLine EF)
    : ∠ b:h:f + ∠ f:g:e < ∟ + ∟ → HB.intersectsLine EF := by
  intro h_lt
  euclid_finish

end Elements.Book1

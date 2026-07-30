import SystemE
import Book1.Prop30.Main
import Book1.Prop44.step12_hal
import Book1.Prop44.step12_fbm
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1
open Elements

theorem h_1_44_s12
    (a b e f g h k l m : Point) (AB BG EF GF AH HB KL : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (heAB : e.onLine AB)
    (hab : a ≠ b)
    (hbet : between a b e)
    (hfGF : f.onLine GF) (hgGF : g.onLine GF)
    (hbBG : b.onLine BG) (hfBG : f.onLine BG)
    (heEF : e.onLine EF) (hgEF : g.onLine EF)
    (hside : f.sameSide b EF)
    (hge : g ≠ e)
    (hGFAB : ¬GF.intersectsLine AB)
    (hBGEF : ¬BG.intersectsLine EF)
    (haAH : a.onLine AH)
    (hAHBG : ¬AH.intersectsLine BG)
    (hAHEF : ¬AH.intersectsLine EF)
    (hhAH : h.onLine AH) (hhGF : h.onLine GF)
    (hhHB : h.onLine HB) (hbHB : b.onLine HB)
    (hkHB : k.onLine HB) (hkEF : k.onLine EF)
    (hkKL : k.onLine KL) (hKLAB : ¬KL.intersectsLine AB)
    (hlAH : l.onLine AH) (hlKL : l.onLine KL)
    (hmBG : m.onLine BG) (hmKL : m.onLine KL)
    : between h a l ∧ between f b m := by
  have hKLGF : ¬KL.intersectsLine GF := by
    euclid_apply (proposition_30 KL GF AB)
    euclid_finish
  have s12_x3 : between h a l := by euclid_apply (h_1_44_s12_x2 a b e f g h k l m AB BG EF GF AH HB KL (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show e.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show between a b e; assumption)) (by (show f.onLine GF; assumption)) (by (show g.onLine GF; assumption)) (by (show b.onLine BG; assumption)) (by (show f.onLine BG; assumption)) (by (show e.onLine EF; assumption)) (by (show g.onLine EF; assumption)) (by (show f.sameSide b EF; assumption)) (by (show g ≠ e; assumption)) (by (show ¬GF.intersectsLine AB; assumption)) (by (show ¬BG.intersectsLine EF; assumption)) (by (show a.onLine AH; assumption)) (by (show ¬AH.intersectsLine BG; assumption)) (by (show ¬AH.intersectsLine EF; assumption)) (by (show h.onLine AH; assumption)) (by (show h.onLine GF; assumption)) (by (show h.onLine HB; assumption)) (by (show b.onLine HB; assumption)) (by (show k.onLine HB; assumption)) (by (show k.onLine EF; assumption)) (by (show k.onLine KL; assumption)) (by (show ¬KL.intersectsLine AB; assumption)) (by (show ¬KL.intersectsLine GF; assumption)) (by (show l.onLine AH; assumption)) (by (show l.onLine KL; assumption)) (by (show m.onLine BG; assumption)) (by (show m.onLine KL; assumption)))
  have s12_x2 : between f b m := by euclid_apply (h_1_44_s12_x1 a b e f g h k l m AB BG EF GF AH HB KL (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show e.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show between a b e; assumption)) (by (show f.onLine GF; assumption)) (by (show g.onLine GF; assumption)) (by (show b.onLine BG; assumption)) (by (show f.onLine BG; assumption)) (by (show e.onLine EF; assumption)) (by (show g.onLine EF; assumption)) (by (show f.sameSide b EF; assumption)) (by (show g ≠ e; assumption)) (by (show ¬GF.intersectsLine AB; assumption)) (by (show ¬BG.intersectsLine EF; assumption)) (by (show a.onLine AH; assumption)) (by (show ¬AH.intersectsLine BG; assumption)) (by (show ¬AH.intersectsLine EF; assumption)) (by (show h.onLine AH; assumption)) (by (show h.onLine GF; assumption)) (by (show h.onLine HB; assumption)) (by (show b.onLine HB; assumption)) (by (show k.onLine HB; assumption)) (by (show k.onLine EF; assumption)) (by (show k.onLine KL; assumption)) (by (show ¬KL.intersectsLine AB; assumption)) (by (show ¬KL.intersectsLine GF; assumption)) (by (show l.onLine AH; assumption)) (by (show l.onLine KL; assumption)) (by (show m.onLine BG; assumption)) (by (show m.onLine KL; assumption)))
  exact ⟨s12_x3, s12_x2⟩

end Elements.Book1

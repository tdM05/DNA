import SystemE
import Book1.Prop44.step13_lnek
import Book1.Prop44.step13_klgf
import Book1.Prop44.step13_hsg
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1
open Elements

theorem h_1_44_s13
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
    (s3 : between g f h)
    (hGFAH : GF.intersectsLine AH)
    (s12 : between h a l ∧ between f b m)
    : formParallelogram h l g k AH EF GF KL := by
  have s13_x4 : l ≠ k := by euclid_apply (h_1_44_s13_x3 a b e f g h k l AB BG EF GF AH KL (by (show g.onLine GF; assumption)) (by (show h.onLine GF; assumption)) (by (show f.onLine GF; assumption)) (by (show k.onLine EF; assumption)) (by (show g.onLine EF; assumption)) (by (show h.onLine AH; assumption)) (by (show l.onLine AH; assumption)) (by (show f.onLine BG; assumption)) (by (show l.onLine KL; assumption)) (by (show k.onLine KL; assumption)) (by (show ¬AH.intersectsLine EF; assumption)) (by (show ¬AH.intersectsLine BG; assumption)) (by (show between g f h; assumption)) (by (show GF.intersectsLine AH; assumption)))
  have s13_x3 : ¬GF.intersectsLine KL := by euclid_apply (h_1_44_s13_x2 a b e f g h k l m AB BG EF GF AH HB KL (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show e.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show between a b e; assumption)) (by (show f.onLine GF; assumption)) (by (show g.onLine GF; assumption)) (by (show b.onLine BG; assumption)) (by (show f.onLine BG; assumption)) (by (show e.onLine EF; assumption)) (by (show g.onLine EF; assumption)) (by (show f.sameSide b EF; assumption)) (by (show g ≠ e; assumption)) (by (show ¬GF.intersectsLine AB; assumption)) (by (show ¬BG.intersectsLine EF; assumption)) (by (show a.onLine AH; assumption)) (by (show ¬AH.intersectsLine BG; assumption)) (by (show ¬AH.intersectsLine EF; assumption)) (by (show h.onLine AH; assumption)) (by (show h.onLine GF; assumption)) (by (show h.onLine HB; assumption)) (by (show b.onLine HB; assumption)) (by (show k.onLine HB; assumption)) (by (show k.onLine EF; assumption)) (by (show k.onLine KL; assumption)) (by (show ¬KL.intersectsLine AB; assumption)) (by (show l.onLine AH; assumption)) (by (show l.onLine KL; assumption)) (by (show m.onLine BG; assumption)) (by (show m.onLine KL; assumption)) (by (show between h a l ∧ between f b m; assumption)) (by (show l ≠ k; assumption)))
  have s13_x2 : h.sameSide g KL := by euclid_apply (h_1_44_s13_x1 a b f g h k l m GF AH KL (by (show h.onLine GF; assumption)) (by (show g.onLine GF; assumption)) (by (show h.onLine AH; assumption)) (by (show l.onLine AH; assumption)) (by (show l.onLine KL; assumption)) (by (show k.onLine KL; assumption)) (by (show l ≠ k; assumption)) (by (show ¬GF.intersectsLine KL; assumption)) (by (show GF.intersectsLine AH; assumption)) (by (show between h a l ∧ between f b m; assumption)))
  exact ⟨hhAH, hlAH, hgEF, hkEF, hhGF, hgGF,
         ⟨hlKL, hkKL, s13_x4⟩, s13_x2, hAHEF, s13_x3⟩

end Elements.Book1

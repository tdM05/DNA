import SystemE
import Book1.Prop17.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1

theorem helper_3_25_step12_eoffac (a b c d e g : Point) (AC AB DB AG : Line)
    (haAC : a.onLine AC) (hcAC : c.onLine AC) (hboff : ¬ b.onLine AC)
    (hbtw : between a d c) (hadb : ∠ a:d:b = ∟)
    (hdDB : d.onLine DB) (hbDB : b.onLine DB) (heDB : e.onLine DB)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hga : g ≠ a) (hgdisj : g.onLine AB ∨ g.sameSide d AB) (hang : ∠ g:a:b = ∠ a:b:d)
    (hgt : ∠ a:b:d > ∠ b:a:d)
    (haAG : a.onLine AG) (hgAG : g.onLine AG) (heAG : e.onLine AG) :
    ¬ e.onLine AC := by
  -- e lies strictly on the opposite side of AC from b (it is the AG∩DB crossing below AC),
  -- so in particular it is off AC.  Reconstruct e's position via Postulate 5.
  euclid_apply (proposition_17 a b d AB DB AC)
  rcases hgdisj with hgAB | hgss
  · exfalso
    euclid_finish
  · euclid_apply (lines_intersect g a b d AG AB DB) as e'
    have hee' : e = e' := by euclid_finish
    euclid_finish

end Elements.Book3

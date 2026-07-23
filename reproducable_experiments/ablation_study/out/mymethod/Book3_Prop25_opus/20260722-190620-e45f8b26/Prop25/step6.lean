import SystemE
import Book1.Prop17.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1

theorem helper_3_25_step6 (a b c d e g : Point) (AC AB DB AG : Line)
    (haAC : a.onLine AC) (hcAC : c.onLine AC) (hboff : ¬ b.onLine AC)
    (hdDB : d.onLine DB) (hbDB : b.onLine DB)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hbtw : between a d c) (hadb : ∠ a:d:b = ∟)
    (hga : g ≠ a) (hgdisj : g.onLine AB ∨ g.sameSide d AB) (hang : ∠ g:a:b = ∠ a:b:d)
    (haAG : a.onLine AG) (hgAG : g.onLine AG)
    (heAG : e.onLine AG) (heDB : e.onLine DB) :
    ∠ b:a:e = ∠ a:b:d ∧ e ≠ a := by
  -- I.17 on triangle a-b-d: ∠a:b:d + ∠b:d:a < 2∟; with ∠b:d:a = ∟ this gives ∠a:b:d < ∟.
  euclid_apply (proposition_17 a b d AB DB AC)
  rcases hgdisj with hgAB | hgss
  · -- g on AB would force ∠g:a:b ∈ {0, 2∟}, contradicting ∠g:a:b = ∠a:b:d ∈ (0, ∟).
    exfalso
    euclid_finish
  · -- Postulate 5: the AG∩DB crossing e' lies on the g-side of AB, so e (= e') is on ray a→g.
    euclid_apply (lines_intersect g a b d AG AB DB) as e'
    have hee' : e = e' := by euclid_finish
    euclid_apply (equal_angles a b b e g AB AG)
    euclid_finish

end Elements.Book3

import SystemE
import Book1.Prop06.Main
import Book1.Prop17.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1

theorem helper_3_25_hEb (a b c d e g3 : Point) (AC AB DB AG3 : Line)
    (haAC : a.onLine AC) (hcAC : c.onLine AC) (hboff : ¬ b.onLine AC)
    (hdDB : d.onLine DB) (hbDB : b.onLine DB)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hbtw : between a d c) (hadb : ∠ a:d:b = ∟)
    (hg3a : g3 ≠ a) (hg3disj : g3.onLine AB ∨ g3.sameSide d AB) (hang : ∠ g3:a:b = ∠ a:b:d)
    (haAG3 : a.onLine AG3) (hg3AG3 : g3.onLine AG3) (heAG3 : e.onLine AG3) (heDB : e.onLine DB) :
    |(e─a)| = |(e─b)| := by
  -- I.17 on triangle a-b-d gives ∠a:b:d < ∟ (with ∠b:d:a = ∟).
  euclid_apply (proposition_17 a b d AB DB AC)
  rcases hg3disj with hg3AB | hg3ss
  · -- g3 on AB would force ∠g3:a:b ∈ {0, 2∟}, contradicting ∠g3:a:b = ∠a:b:d ∈ (0, ∟).
    exfalso
    euclid_finish
  · -- Postulate 5: the AG3∩DB crossing e' lies on the g3-side of AB, so e (= e').
    euclid_apply (lines_intersect g3 a b d AG3 AB DB) as e'
    have hee' : e = e' := by euclid_finish
    -- ∠b:a:e = ∠b:a:g3 (= ∠a:b:d): e on ray a→g3.
    euclid_apply (equal_angles a b b e g3 AB AG3)
    -- ∠a:b:e = ∠a:b:d: e on ray b→d.
    euclid_apply (equal_angles b a a e d AB DB)
    -- Triangle e-b-a: ∠e:b:a = ∠e:a:b ⟹ |e─b| = |e─a| [I.6].
    euclid_apply (proposition_6 e b a DB AB AG3)
    euclid_finish

end Elements.Book3

import SystemE
import Book1.Prop17.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1

theorem helper_3_25_step22 (a b c d e g3 : Point) (AC AB DB AG3 : Line)
    (haAG3 : a.onLine AG3) (hg3AG3 : g3.onLine AG3) (heAG3 : e.onLine AG3)
    (heDB : e.onLine DB) (hdDB : d.onLine DB) (hbDB : b.onLine DB)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hg3a : g3 ≠ a)
    (hg3disj : g3.onLine AB ∨ g3.sameSide d AB)
    (hang : ∠ g3:a:b = ∠ a:b:d)
    (hadb : ∠ a:d:b = ∟)
    (haAC : a.onLine AC) (hcAC : c.onLine AC)
    (hbtw : between a d c) (hboff : ¬ b.onLine AC)
    (hassump1 : ∠ a:b:d < ∠ b:a:d)   -- "$ABD$ is less than $BAD$"
    : e.onLine DB ∧ e.sameSide b AC := by
  refine ⟨heDB, ?_⟩
  rcases hg3disj with hg3AB | hg3ss
  · -- g3 on AB ⟹ AG3 = AB, so e is the AB∩DB crossing = b, same side (trivially)
    euclid_finish
  · -- g3 strictly on the d-side of AB ⟹ reconstruct e via Postulate 5, pinning its position.
    euclid_apply (proposition_17 a b d AB DB AC)
    euclid_apply (lines_intersect g3 a b d AG3 AB DB) as e'
    have hee' : e = e' := by euclid_finish
    euclid_finish

end Elements.Book3

import SystemE
import Book1.Prop17.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1

theorem helper_3_25_hAG3DB (a b c d g3 : Point) (AC AB AG3 DB : Line)
    (haAG3 : a.onLine AG3) (hg3AG3 : g3.onLine AG3)
    (hdDB : d.onLine DB) (hbDB : b.onLine DB)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hg3a : g3 ≠ a)
    (hg3disj : g3.onLine AB ∨ g3.sameSide d AB)
    (hang : ∠ g3:a:b = ∠ a:b:d)
    (hadb : ∠ a:d:b = ∟)
    (haAC : a.onLine AC) (hcAC : c.onLine AC)
    (hbtw : between a d c) (hboff : ¬ b.onLine AC) :
    AG3.intersectsLine DB := by
  rcases hg3disj with hg3AB | hg3ss
  · -- g3 on AB ⟹ AG3 = AB, which meets DB at the common point b
    euclid_finish
  · -- g3 strictly on the d-side of AB ⟹ Postulate 5 (lines_intersect).
    euclid_apply (proposition_17 a b d AB DB AC)
    euclid_apply (lines_intersect g3 a b d AG3 AB DB) as e'
    euclid_finish

end Elements.Book3

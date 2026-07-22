import SystemE
import Book1Variants.Prop29
import Book1.Prop17.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1
open Elements

theorem helper_3_25_hAG3DB (a b c d g3 : Point) (AC DB AB AG3 : Line)
    (haAC : a.onLine AC) (hcAC : c.onLine AC) (hac : a ≠ c) (hboff : ¬b.onLine AC)
    (hadc : between a d c) (haddc : |(a─d)| = |(d─c)|)
    (hdDB : d.onLine DB) (hbDB : b.onLine DB)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hab : a ≠ b)
    (hadbperp : ∠ a:d:b = ∟)
    (hg3a : g3 ≠ a) (hg3side : g3.onLine AB ∨ g3.sameSide d AB)
    (hg3ab : ∠ g3:a:b = ∠ a:b:d)
    (haAG3 : a.onLine AG3) (hg3AG3 : g3.onLine AG3) :
    AG3.intersectsLine DB := by
  by_contra hnpar
  rcases hg3side with hg3AB | hg3ss
  · -- g3 on AB is impossible: ∠ g3:a:b = ∠ a:b:d ∈ (0, ∟), not 0 or 2∟
    euclid_apply (proposition_17 a b d AB DB AC)
    euclid_finish
  · -- g3 strictly off AB, on d's side: co-interior angles force ∠ a:b:d = ∟, contradicting prop 17
    euclid_apply (proposition_29''''' g3 d a b AG3 DB AB)
    euclid_apply (proposition_17 a b d AB DB AC)
    euclid_finish

end Elements.Book3

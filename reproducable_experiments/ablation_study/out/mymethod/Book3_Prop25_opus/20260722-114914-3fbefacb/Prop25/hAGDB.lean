import SystemE
import Book1Variants.Prop29
import Book1.Prop17.Main
import Helpers.Angle
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1
open Elements

theorem helper_3_25_hAGDB (a b c d g : Point) (AC DB AB AG : Line)
    (haAC : a.onLine AC) (hcAC : c.onLine AC) (hac : a ≠ c) (hboff : ¬b.onLine AC)
    (hadc : between a d c) (haddc : |(a─d)| = |(d─c)|)
    (hdDB : d.onLine DB) (hbDB : b.onLine DB)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hab : a ≠ b)
    (hadbperp : ∠ a:d:b = ∟)
    (hgt : ∠ a:b:d > ∠ b:a:d)
    (hga : g ≠ a) (hgside : g.onLine AB ∨ g.sameSide d AB)
    (hgab : ∠ g:a:b = ∠ a:b:d)
    (haAG : a.onLine AG) (hgAG : g.onLine AG) :
    AG.intersectsLine DB := by
  by_contra hnpar
  rcases hgside with hgAB | hgss
  · -- g on AB is impossible: ∠ g:a:b = ∠ a:b:d ∈ (0, ∟), not 0 or 2∟
    euclid_apply (proposition_17 a b d AB DB AC)
    euclid_finish
  · -- g strictly off AB, on d's side
    have hgbopp : g.opposingSides b AC := by euclid_finish
    euclid_apply (angle_split a b g d AB AG)
    euclid_apply (proposition_29''' g b a d AG DB AC)
    euclid_apply (proposition_17 a b d AB DB AC)
    euclid_finish

end Elements.Book3

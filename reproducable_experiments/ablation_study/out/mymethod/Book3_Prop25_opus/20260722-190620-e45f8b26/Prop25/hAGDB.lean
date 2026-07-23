import SystemE
import Book1.Prop17.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1

theorem helper_3_25_hAGDB (a b c d g : Point) (AC AB AG DB : Line)
    (haAG : a.onLine AG) (hgAG : g.onLine AG)
    (hdDB : d.onLine DB) (hbDB : b.onLine DB)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hga : g ≠ a)
    (hgdisj : g.onLine AB ∨ g.sameSide d AB)
    (hang : ∠ g:a:b = ∠ a:b:d)
    (hgt : ∠ a:b:d > ∠ b:a:d)
    (hadb : ∠ a:d:b = ∟)
    (haAC : a.onLine AC) (hcAC : c.onLine AC)
    (hbtw : between a d c) (hmid : |(a─d)| = |(d─c)|)
    (hlen : |(a─b)| = |(c─b)|) (hboff : ¬ b.onLine AC) :
    AG.intersectsLine DB := by
  rcases hgdisj with hgAB | hgss
  · -- g on AB ⟹ AG = AB, which meets DB at the common point b
    euclid_finish
  · -- g strictly on the d-side of AB ⟹ Postulate 5 (lines_intersect).
    -- I.17: in triangle a-b-d the two angles ∠a:b:d + ∠b:d:a < 2∟; with ∠b:d:a = ∟
    -- this makes ∠a:b:d < ∟, so ∠g:a:b + ∠a:b:d = 2·∠a:b:d < 2∟.
    euclid_apply (proposition_17 a b d AB DB AC)
    euclid_apply (lines_intersect g a b d AG AB DB) as e'
    euclid_finish

end Elements.Book3

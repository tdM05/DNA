import SystemE
import Book1.Prop17.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_hAGDB (a b c d g : Point) (AC DB AB AG : Line)
    (haAC : a.onLine AC) (hcAC : c.onLine AC) (hac : a ≠ c)
    (hbAC : ¬b.onLine AC) (hab_cb : |(a─b)| = |(c─b)|)
    (hbet : between a d c) (had_dc : |(a─d)| = |(d─c)|)
    (hdDB : d.onLine DB) (hbDB : b.onLine DB)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hadb : ∠ a:d:b = ∟) (hgt : ∠ a:b:d > ∠ b:a:d)
    (hga : g ≠ a) (hgAB : g.onLine AB ∨ g.sameSide d AB)
    (hgab : ∠ g:a:b = ∠ a:b:d)
    (haAG : a.onLine AG) (hgAG : g.onLine AG) :
    AG.intersectsLine DB := by
  -- ∠abd < ∟ : angles at b and d of right triangle abd sum to < 2∟, and ∠adb = ∟.
  euclid_apply (Elements.Book1.proposition_17 a b d AB DB AC)
  -- g is off AB (its angle to AB is a proper acute angle), so it lies on d's side of AB.
  have hgsd : g.sameSide d AB := by
    rcases hgAB with h | h
    · exfalso; euclid_finish
    · exact h
  -- Postulate 5 (transversal AB, co-interior sum ∠gab + ∠abd = 2∠abd < 2∟): AG and DB meet.
  euclid_apply (lines_intersect g a b d AG AB DB) as e
  euclid_apply (intersection_lines_common_point e AG DB)
  euclid_finish

end Elements.Book3

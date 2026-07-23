import SystemE
import Book1.Prop17.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_hAG3DB (a b c d g3 : Point) (AC DB AB AG3 : Line)
    (haAC : a.onLine AC) (hcAC : c.onLine AC) (hac : a ≠ c)
    (hbAC : ¬b.onLine AC) (hab_cb : |(a─b)| = |(c─b)|)
    (hbet : between a d c) (had_dc : |(a─d)| = |(d─c)|)
    (hdDB : d.onLine DB) (hbDB : b.onLine DB)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hadb : ∠ a:d:b = ∟)
    (hga : g3 ≠ a) (hgAB : g3.onLine AB ∨ g3.sameSide d AB)
    (hgab : ∠ g3:a:b = ∠ a:b:d)
    (haAG3 : a.onLine AG3) (hgAG3 : g3.onLine AG3) :
    AG3.intersectsLine DB := by
  -- ∠abd < ∟ (right triangle abd), g3 on d's side of AB.
  euclid_apply (Elements.Book1.proposition_17 a b d AB DB AC)
  have hgsd : g3.sameSide d AB := by
    rcases hgAB with h | h
    · exfalso; euclid_finish
    · exact h
  -- Postulate 5 (transversal AB, co-interior sum ∠g3ab + ∠abd = 2∠abd < 2∟): AG3 and DB meet.
  euclid_apply (lines_intersect g3 a b d AG3 AB DB) as e
  euclid_apply (intersection_lines_common_point e AG3 DB)
  euclid_finish

end Elements.Book3

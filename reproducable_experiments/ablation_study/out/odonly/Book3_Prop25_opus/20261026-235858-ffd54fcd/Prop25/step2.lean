import SystemE
import Book1.Prop11.Main
import Book1.Prop08.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_step2 (a b c d : Point) (AC DB AB : Line)
    (ha_AC : a.onLine AC) (hc_AC : c.onLine AC) (hac : a ≠ c)
    (hb_off : ¬b.onLine AC) (hbeq : |(a─b)| = |(c─b)|)
    (hadc : between a d c) (hadeq : |(a─d)| = |(d─c)|)
    (hd_DB : d.onLine DB) (hb_DB : b.onLine DB)
    (ha_AB : a.onLine AB) (hb_AB : b.onLine AB) :
    ∠ a:d:b = ∟ := by
  -- Euclid erects DB perpendicular to AC at D [Prop.~1.11]
  euclid_apply (Elements.Book1.proposition_11 a c d AC) as p
  -- B lies on that perpendicular: triangles ADB, CDB are congruent (SSS), so ∠ADB = ∠CDB
  euclid_apply (line_from_points c b) as CB
  euclid_apply (Elements.Book1.proposition_8 d a b d c b AC AB DB AC CB DB)
  euclid_finish

end Elements.Book3

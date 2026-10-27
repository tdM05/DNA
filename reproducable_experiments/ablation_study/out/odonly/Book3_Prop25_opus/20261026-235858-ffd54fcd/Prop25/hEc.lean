import SystemE
import Book1.Prop04.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_hEc (a b c d e : Point) (AC DB AG3 : Line)
    (ha_AC : a.onLine AC) (hc_AC : c.onLine AC) (hac : a ≠ c)
    (hb_off : ¬b.onLine AC) (hadc : between a d c) (hadeq : |(a─d)| = |(d─c)|)
    (hd_DB : d.onLine DB) (hb_DB : b.onLine DB)
    (ha_AG3 : a.onLine AG3) (he_AG3 : e.onLine AG3) (he_DB : e.onLine DB)
    (hstep2 : ∠ a:d:b = ∟)
    (hstep22 : e.onLine DB ∧ e.sameSide b AC) :
    |(e─a)| = |(e─c)| := by
  obtain ⟨_, hesb⟩ := hstep22
  -- e is off AC (same side as b), and E lies on the perpendicular DB at midpoint D
  have he_off : ¬ e.onLine AC := by euclid_finish
  have hfT1 : formTriangle d a e AC AG3 DB := by euclid_finish
  euclid_apply (line_from_points c e) as CE3
  have hfT2 : formTriangle d c e AC CE3 DB := by euclid_finish
  -- SAS on triangles ADE, CDE: AD=CD, DE common, ∠ADE=∠CDE=∟ ⟹ AE=CE [Prop.~1.4]
  euclid_apply (Elements.Book1.proposition_4 d a e d c e AC AG3 DB AC CE3 DB)
  euclid_finish

end Elements.Book3

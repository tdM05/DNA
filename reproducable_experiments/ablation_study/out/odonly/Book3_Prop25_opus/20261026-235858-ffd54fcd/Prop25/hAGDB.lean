import SystemE
import Book1.Prop32.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_hAGDB (a b c d g : Point) (AC DB AB AG : Line)
    (ha_AC : a.onLine AC) (hc_AC : c.onLine AC) (hac : a ≠ c)
    (hb_off : ¬b.onLine AC) (hadc : between a d c)
    (hd_DB : d.onLine DB) (hb_DB : b.onLine DB)
    (ha_AB : a.onLine AB) (hb_AB : b.onLine AB) (hab : a ≠ b)
    (hstep2 : ∠ a:d:b = ∟)
    (hga : g ≠ a) (hgab : ∠ g:a:b = ∠ a:b:d)
    (hg_side : g.onLine AB ∨ g.sameSide d AB)
    (ha_AG : a.onLine AG) (hg_AG : g.onLine AG) :
    AG.intersectsLine DB := by
  -- right triangle ABD has its right angle at D, so ∠ABD < ∟
  euclid_apply (extend_point DB b d) as e'
  euclid_apply (Elements.Book1.proposition_32 a b d e' AB DB AC)
  have hacute : ∠ a:b:d < ∟ := by euclid_finish
  -- g lies strictly on d's side of AB (ruling out g.onLine AB, since ∠gab = ∠abd > 0)
  have hgside : g.sameSide d AB := by euclid_finish
  -- equal co-interior angles summing < 2∟ ⟹ AG meets DB (Euclid's Postulate 5)
  euclid_apply (lines_intersect g a b d AG AB DB) as e
  euclid_finish

end Elements.Book3

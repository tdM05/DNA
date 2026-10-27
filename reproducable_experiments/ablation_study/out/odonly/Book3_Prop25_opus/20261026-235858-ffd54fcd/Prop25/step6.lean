import SystemE
import Book1.Prop32.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_step6 (a b c d g e : Point) (AC DB AB AG : Line)
    (ha_AC : a.onLine AC) (hc_AC : c.onLine AC) (hac : a ≠ c)
    (hb_off : ¬b.onLine AC) (hadc : between a d c)
    (hd_DB : d.onLine DB) (hb_DB : b.onLine DB)
    (ha_AB : a.onLine AB) (hb_AB : b.onLine AB) (hab : a ≠ b)
    (hstep2 : ∠ a:d:b = ∟)
    (hga : g ≠ a) (hgab : ∠ g:a:b = ∠ a:b:d)
    (hg_side : g.onLine AB ∨ g.sameSide d AB)
    (ha_AG : a.onLine AG) (hg_AG : g.onLine AG)
    (he_AG : e.onLine AG) (he_DB : e.onLine DB) :
    ∠ b:a:e = ∠ a:b:d ∧ e ≠ a := by
  -- re-establish the P5 intersection on g's side of AB, then identify it with e by uniqueness
  euclid_apply (extend_point DB b d) as e'
  euclid_apply (Elements.Book1.proposition_32 a b d e' AB DB AC)
  have hacute : ∠ a:b:d < ∟ := by euclid_finish
  have hgside : g.sameSide d AB := by euclid_finish
  euclid_apply (lines_intersect g a b d AG AB DB) as f
  have heside : e.sameSide g AB := by euclid_finish
  euclid_finish

end Elements.Book3

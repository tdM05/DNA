import SystemE
import Book1.Prop32.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_step22 (a b c d g3 e : Point) (AC DB AB AG3 : Line)
    (ha_AC : a.onLine AC) (hc_AC : c.onLine AC) (hac : a ≠ c)
    (hb_off : ¬b.onLine AC) (hadc : between a d c)
    (hd_DB : d.onLine DB) (hb_DB : b.onLine DB)
    (ha_AB : a.onLine AB) (hb_AB : b.onLine AB) (hab : a ≠ b)
    (hstep2 : ∠ a:d:b = ∟)
    (hga : g3 ≠ a) (hgab : ∠ g3:a:b = ∠ a:b:d)
    (hg_side : g3.onLine AB ∨ g3.sameSide d AB)
    (ha_AG3 : a.onLine AG3) (hg_AG3 : g3.onLine AG3)
    (he_AG3 : e.onLine AG3) (he_DB : e.onLine DB)
  -- Reasoning hypotheses (from @assumption — keep these types in the signature):
  (hassump1 : ∠ a:b:d < ∠ b:a:d)   -- "$ABD$ is less than $BAD$"
  : e.onLine DB ∧ e.sameSide b AC := by
  -- re-establish the P5 intersection on g3's side of AB, then identify it with e by uniqueness
  euclid_apply (extend_point DB b d) as e'
  euclid_apply (Elements.Book1.proposition_32 a b d e' AB DB AC)
  have hacute : ∠ a:b:d < ∟ := by euclid_finish
  have hgside : g3.sameSide d AB := by euclid_finish
  euclid_apply (lines_intersect g3 a b d AG3 AB DB) as f
  have heside : e.sameSide g3 AB := by euclid_finish
  -- ∠BAE = ∠ABD < ∠BAD ⟹ E falls on B's side of AC (inside the segment)
  euclid_finish

end Elements.Book3

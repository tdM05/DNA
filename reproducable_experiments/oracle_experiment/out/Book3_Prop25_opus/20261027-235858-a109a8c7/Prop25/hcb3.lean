import SystemE
import Book1.Prop06.Main
import Book1.Prop17.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3
open Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_3_25_hcb3 (a b c d e e0p : Point) (AC DB AB AE : Line) (α : Circle)
    (haAC : a.onLine AC) (hcAC : c.onLine AC) (hbAC : ¬b.onLine AC) (hadc : between a d c)
    (hdDB : d.onLine DB) (hbDB : b.onLine DB) (heDB : e.onLine DB) (hstep2 : ∠ a:d:b = ∟)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hab : a ≠ b)
    (he0p_ang : ∠ e0p:a:b = ∠ a:b:d) (he0p_side : e0p.sameSide d AB)
    (haAE : a.onLine AE) (he0pAE : e0p.onLine AE) (heAE : e.onLine AE)
    (hcentre : e.isCentre α) (haC : a.onCircle α) (hstep21b : ∠ b:a:e = ∠ a:b:d) :
    b.onCircle α := by
  -- e, d on the same side of AB and b = AB ∩ DB, so b is not between e and d: ray b→e = ray b→d.
  euclid_apply (proposition_17 a d b AC DB AB)
  euclid_apply (lines_intersect e0p a b d AE AB DB) as eW
  have hesd : e.sameSide d AB := by euclid_finish
  have hray : ∠ a:b:e = ∠ a:b:d := by
    euclid_apply (equal_angles b a a e d AB DB)
    euclid_finish
  -- isosceles △AEB: ∠EAB = ∠EBA ⟹ EA = EB [Prop.~1.6]; equidistant ⟹ B on the circle.
  have hbAE : ¬ b.onLine AE := by euclid_finish
  have htri : formTriangle e a b AE AB DB := by
    refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> euclid_finish
  euclid_apply (proposition_6 e a b AE AB DB)
  euclid_apply (point_on_circle_if e a b α)
  euclid_finish

end Elements.Book3

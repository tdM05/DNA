import SystemE
import Book1.Prop04.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3
open Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_3_25_hcc3 (a b c d e : Point) (AC DB AE : Line) (α : Circle)
    (haAC : a.onLine AC) (hcAC : c.onLine AC) (hbAC : ¬b.onLine AC) (hadc : between a d c)
    (hdDB : d.onLine DB) (hbDB : b.onLine DB) (heDB : e.onLine DB) (hstep2 : ∠ a:d:b = ∟)
    (haAE : a.onLine AE) (heAE : e.onLine AE) (hstep1 : |(a─d)| = |(d─c)|)
    (hstep22 : e.sameSide b AC)
    (hcentre : e.isCentre α) (haC : a.onCircle α) : c.onCircle α := by
  -- SAS △ADE ≅ △CDE (DA=DC, DE common, ∠ADE=∠CDE=∟) ⟹ AE=CE [Prop.~1.4]; equidistant ⟹ C on circle.
  euclid_apply (line_from_points c e) as EC
  have heAC : ¬ e.onLine AC := by euclid_finish
  have htri1 : formTriangle d a e AC AE DB := by
    refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> euclid_finish
  have htri2 : formTriangle d c e AC EC DB := by
    refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> euclid_finish
  euclid_apply (proposition_4 d a e d c e AC AE DB AC EC DB)
  euclid_apply (point_on_circle_if e a c α)
  euclid_finish

end Elements.Book3

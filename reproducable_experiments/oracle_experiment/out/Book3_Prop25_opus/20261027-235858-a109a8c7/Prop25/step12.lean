import SystemE
import Book1.Prop04.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3
open Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_3_25_step12 (a b c d e : Point) (AC AE DB EC : Line)
    (haAC : a.onLine AC) (hcAC : c.onLine AC) (hbAC : ¬b.onLine AC) (hadc : between a d c)
    (hdDB : d.onLine DB) (hbDB : b.onLine DB) (heDB : e.onLine DB)
    (haAE : a.onLine AE) (heAE : e.onLine AE) (hcEC : c.onLine EC) (heEC : e.onLine EC)
    (hbde : between b d e)
    (hstep10 : |(a─d)| = |(c─d)| ∧ |(d─e)| = |(d─e)|) (hstep11 : ∠ a:d:e = ∠ c:d:e) :
    |(a─e)| = |(c─e)| := by
  -- SAS on △DAE ≅ △DCE: DA=DC, DE common, ∠ADE=∠CDE ⟹ AE=CE [Prop.~1.4].
  have heAC : ¬ e.onLine AC := by euclid_finish
  have htri1 : formTriangle d a e AC AE DB := by
    refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> euclid_finish
  have htri2 : formTriangle d c e AC EC DB := by
    refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> euclid_finish
  euclid_apply (proposition_4 d a e d c e AC AE DB AC EC DB)
  euclid_finish

end Elements.Book3

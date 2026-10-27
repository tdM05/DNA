import SystemE
import Book1.Prop47.Main
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1

theorem helper_3_36_step23 (a c d e f : Point) (ABC : Circle) (DA EF EC : Line)
  (haDA : a.onLine DA) (hdDA : d.onLine DA) (hbdca : between d c a)
  (hfDA : f.onLine DA) (hfEF : f.onLine EF) (heEF : e.onLine EF)
  (heEC : e.onLine EC) (hcEC : c.onLine EC)
  (hccirc : c.onCircle ABC) (hecentre : e.isCentre ABC)
  (hhalf : |(a─f)| = |(f─c)|)
  (hnotthrough : ¬∃ g : Point, g.isCentre ABC ∧ g.onLine DA)
  -- Reasoning hypotheses (from @assumption — keep these types in the signature):
  (hassump1 : ∠ e:f:c = ∟)   -- "$EFC$ [is] a right-angle"
  : |(e─c)| * |(e─c)| = |(f─c)| * |(f─c)| + |(e─f)| * |(e─f)| := by
  have hcDA : c.onLine DA := by euclid_finish
  have hennotDA : ¬ e.onLine DA := fun h => hnotthrough ⟨e, hecentre, h⟩
  have hac : a ≠ c := by euclid_finish
  have hfc : f ≠ c := by euclid_finish
  have hec : e ≠ c := by euclid_finish
  have hef : e ≠ f := by euclid_finish
  euclid_apply (proposition_47 f e c EF EC DA)
  euclid_finish

end Elements.Book3

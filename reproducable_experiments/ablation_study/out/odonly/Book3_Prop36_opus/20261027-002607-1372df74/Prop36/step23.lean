import SystemE
import Book1.Prop47.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1

theorem helper_3_36_step23
  (a c d e f : Point) (ABC : Circle) (DA EF EC : Line)
  (haDA : a.onLine DA) (hdDA : d.onLine DA)
  (hbet_dca : between d c a)
  (hfDA : f.onLine DA)
  (he : e.isCentre ABC)
  (hnotthrough : ¬∃ g : Point, g.isCentre ABC ∧ g.onLine DA)
  (heEF : e.onLine EF) (hfEF : f.onLine EF)
  (heEC : e.onLine EC) (hcEC : c.onLine EC)
  (step17 : |(a─f)| = |(f─c)|)
  (hassump1 : ∠ e:f:c = ∟)   -- "$EFC$ [is] a right-angle"
  : |(e─c)| * |(e─c)| = |(f─c)| * |(f─c)| + |(e─f)| * |(e─f)| := by
  have hnoteDA : ¬e.onLine DA := fun h => hnotthrough ⟨e, he, h⟩
  have hac : a ≠ c := by euclid_finish
  have hcf : c ≠ f := by euclid_finish
  have hcDA : c.onLine DA := by euclid_finish
  euclid_apply (Elements.Book1.proposition_47 f e c EF EC DA)
  euclid_finish

end Elements.Book3

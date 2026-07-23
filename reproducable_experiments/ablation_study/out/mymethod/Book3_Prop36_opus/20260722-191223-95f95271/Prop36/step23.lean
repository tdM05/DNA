import SystemE
import Book1.Prop47.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step23
  (a c d e f : Point) (ABC : Circle) (DA EF EC : Line)
  (ha_DA : a.onLine DA) (hd_DA : d.onLine DA) (hf_DA : f.onLine DA)
  (he_EF : e.onLine EF) (hf_EF : f.onLine EF)
  (he_EC : e.onLine EC) (hc_EC : c.onLine EC)
  (hbet : between d c a)
  (hecenter : e.isCentre ABC)
  (hnotthrough : ¬∃ p : Point, p.isCentre ABC ∧ p.onLine DA)
  (hstep17 : |(a─f)| = |(f─c)|)
  -- Reasoning hypotheses (from @assumption — keep these types in the signature):
  (hassump1 : ∠ e:f:c = ∟)   -- "$EFC$ [is] a right-angle"
  : |(e─c)| * |(e─c)| = |(f─c)| * |(f─c)| + |(e─f)| * |(e─f)| := by
  have hc_DA : c.onLine DA := by euclid_finish
  have hnotDA : ¬ e.onLine DA := fun he => hnotthrough ⟨e, hecenter, he⟩
  euclid_apply (Elements.Book1.proposition_47 f e c EF EC DA)
  euclid_finish

end Elements.Book3

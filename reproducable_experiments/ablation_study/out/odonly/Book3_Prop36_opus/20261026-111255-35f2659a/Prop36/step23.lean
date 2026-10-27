import SystemE
import Book1.Prop47.Main
import Book3.Prop36.step23_tri
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step23 (a c d e f : Point) (DA EF EC : Line)
  (haDA : a.onLine DA) (hdDA : d.onLine DA) (hfDA : f.onLine DA)
  (hdca : between d c a)
  (heEF : e.onLine EF) (hfEF : f.onLine EF)
  (heEC : e.onLine EC) (hcEC : c.onLine EC)
  (henef : e ≠ f) (hhalf : |(a─f)| = |(f─c)|)
  -- Reasoning hypotheses (from @assumption — keep these types in the signature):
  (hassump1 : ∠ e:f:c = ∟)   -- "$EFC$ [is] a right-angle"
  : |(e─c)| * |(e─c)| = |(f─c)| * |(f─c)| + |(e─f)| * |(e─f)| := by
  have hcDA : c.onLine DA := by euclid_finish
  have hfnec : f ≠ c := by euclid_finish
  have heoff : ¬ e.onLine DA := by euclid_finish
  have step23_tri : formTriangle f e c EF EC DA := by euclid_apply (helper_3_36_step23_tri c e f DA EF EC (by euclid_assumption "" (show f.onLine DA; assumption)) (by euclid_assumption "" (show c.onLine DA; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show e.onLine EC; assumption)) (by euclid_assumption "" (show c.onLine EC; assumption)) (by euclid_assumption "" (show e ≠ f; assumption)) (by euclid_assumption "" (show f ≠ c; assumption)) (by euclid_assumption "" (show ¬ e.onLine DA; assumption)))
  euclid_apply (Elements.Book1.proposition_47 f e c EF EC DA ⟨step23_tri, hassump1⟩)
  euclid_finish

end Elements.Book3

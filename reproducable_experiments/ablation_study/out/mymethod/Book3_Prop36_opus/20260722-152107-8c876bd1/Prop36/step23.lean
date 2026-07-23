import SystemE
import Book3.Prop36.step23_tri
import Book3.Prop36.step23_pyth
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step23 (a c d e f : Point) (ABC : Circle) (DA EF EC : Line)
  (ha_DA : a.onLine DA) (hd_DA : d.onLine DA) (hf_DA : f.onLine DA)
  (hbtw_dca : between d c a)
  (he_EF : e.onLine EF) (hf_EF : f.onLine EF)
  (he_EC : e.onLine EC) (hc_EC : c.onLine EC)
  (he_centre : e.isCentre ABC) (hc_circ : c.onCircle ABC)
  (hnotthrough : ¬∃ g : Point, g.isCentre ABC ∧ g.onLine DA)
  (hbisect : |(a─f)| = |(f─c)|)
  -- Reasoning hypotheses (from @assumption — keep these types in the signature):
  (hassump1 : ∠ e:f:c = ∟)   -- "$EFC$ [is] a right-angle"
  : |(e─c)| * |(e─c)| = |(f─c)| * |(f─c)| + |(e─f)| * |(e─f)| := by
  have step23_tri : formTriangle f e c EF EC DA := by euclid_apply (helper_3_36_step23_tri a c d e f ABC DA EF EC (by euclid_assumption "" (show a.onLine DA; assumption)) (by euclid_assumption "" (show d.onLine DA; assumption)) (by euclid_assumption "" (show f.onLine DA; assumption)) (by euclid_assumption "" (show between d c a; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show e.onLine EC; assumption)) (by euclid_assumption "" (show c.onLine EC; assumption)) (by euclid_assumption "" (show e.isCentre ABC; assumption)) (by euclid_assumption "" (show c.onCircle ABC; assumption)) (by euclid_assumption "" (show ¬∃ g : Point, g.isCentre ABC ∧ g.onLine DA; assumption)) (by euclid_assumption "" (show |(a─f)| = |(f─c)|; assumption)) (by euclid_assumption "" (show ∠ e:f:c = ∟; assumption)))
  have step23_pyth : |(e─c)| * |(e─c)| = |(e─f)| * |(e─f)| + |(f─c)| * |(f─c)| := by euclid_apply (helper_3_36_step23_pyth c e f DA EF EC (by euclid_assumption "" (show formTriangle f e c EF EC DA; assumption)) (by euclid_assumption "" (show ∠ e:f:c = ∟; assumption)))
  rw [step23_pyth]; ring

end Elements.Book3

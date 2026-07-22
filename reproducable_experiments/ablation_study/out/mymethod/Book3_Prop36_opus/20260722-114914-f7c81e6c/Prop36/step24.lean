import SystemE
import Book3.Prop36.step24_df
import Book3.Prop36.step24_tri
import Book3.Prop36.step24_p47
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step24
  (a c d e f : Point) (ABC : Circle) (DA ED EF : Line)
  (haDA : a.onLine DA) (hdDA : d.onLine DA) (hfDA : f.onLine DA)
  (hbdca : between d c a)
  (hdED : d.onLine ED) (heED : e.onLine ED)
  (hfEF : f.onLine EF) (heEF : e.onLine EF)
  (step13 : e.isCentre ABC)
  (step17 : |(a─f)| = |(f─c)|)
  (hnotthrough : ¬(∃ g : Point, g.isCentre ABC ∧ g.onLine DA))
  (hperp : ∀ p : Point, p.onLine DA → p ≠ f → ∠ p:f:e = ∟)
  : |(e─d)| * |(e─d)| = |(d─f)| * |(d─f)| + |(f─e)| * |(f─e)| := by
  have hnotDA : ¬ e.onLine DA := fun he => hnotthrough ⟨e, step13, he⟩
  have step24_df : d ≠ f := by euclid_apply (helper_3_36_step24_df a c d f DA (by euclid_assumption "" (show a.onLine DA; assumption)) (by euclid_assumption "" (show d.onLine DA; assumption)) (by euclid_assumption "" (show f.onLine DA; assumption)) (by euclid_assumption "" (show between d c a; assumption)) (by euclid_assumption "" (show |(a─f)| = |(f─c)|; assumption)))
  have hdfe : ∠ d:f:e = ∟ := hperp d hdDA step24_df
  have step24_tri : formTriangle f d e DA ED EF := by euclid_apply (helper_3_36_step24_tri d e f DA ED EF (by euclid_assumption "" (show f.onLine DA; assumption)) (by euclid_assumption "" (show d.onLine DA; assumption)) (by euclid_assumption "" (show d.onLine ED; assumption)) (by euclid_assumption "" (show e.onLine ED; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show ¬ e.onLine DA; assumption)) (by euclid_assumption "" (show d ≠ f; assumption)))
  have step24_p47 : |(e─d)| * |(e─d)| = |(d─f)| * |(d─f)| + |(f─e)| * |(f─e)| := by euclid_apply (helper_3_36_step24_p47 d e f DA ED EF (by euclid_assumption "" (show formTriangle f d e DA ED EF; assumption)) (by euclid_assumption "" (show ∠ d:f:e = ∟; assumption)))
  exact step24_p47

end Elements.Book3

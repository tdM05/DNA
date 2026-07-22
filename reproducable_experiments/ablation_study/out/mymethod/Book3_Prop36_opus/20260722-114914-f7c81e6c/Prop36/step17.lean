import SystemE
import Book3.Prop36.step17_facts
import Book3.Prop36.step17_fa
import Book3.Prop36.step17_pa
import Book3.Prop36.step17_lt
import Book3.Prop36.step17_bet
import Book3.Prop36.step17_p3
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step17
  (a c d e f : Point) (ABC : Circle) (DA EF EC : Line)
  (ha : a.onCircle ABC) (hc : c.onCircle ABC)
  (haDA : a.onLine DA) (hdDA : d.onLine DA)
  (hbdca : between d c a)
  (hfDA : f.onLine DA) (hfEF : f.onLine EF)
  (heEC : e.onLine EC) (hcEC : c.onLine EC)
  (hperp : ∀ p : Point, p.onLine DA → p ≠ f → ∠ p:f:e = ∟)
  (step17_assumption1 : e.isCentre ABC ∧ e.onLine EF ∧ ¬e.onLine DA ∧ (∠ a:f:e = ∟ ∨ ∠ c:f:e = ∟))
  : |(a─f)| = |(f─c)| := by
  obtain ⟨hcentre, heEF, hnotDA, hang⟩ := step17_assumption1
  have step17_facts : c.onLine DA ∧ a ≠ c := by euclid_apply (helper_3_36_step17_facts a c d DA (by euclid_assumption "" (show a.onLine DA; assumption)) (by euclid_assumption "" (show d.onLine DA; assumption)) (by euclid_assumption "" (show between d c a; assumption)))
  obtain ⟨hcDA, hac⟩ := step17_facts
  have step17_fa : f ≠ a := by euclid_apply (helper_3_36_step17_fa a c e f ABC DA (by euclid_assumption "" (show a.onCircle ABC; assumption)) (by euclid_assumption "" (show c.onCircle ABC; assumption)) (by euclid_assumption "" (show e.isCentre ABC; assumption)) (by euclid_assumption "" (show a.onLine DA; assumption)) (by euclid_assumption "" (show c.onLine DA; assumption)) (by euclid_assumption "" (show f.onLine DA; assumption)) (by euclid_assumption "" (show ¬ e.onLine DA; assumption)) (by euclid_assumption "" (show ∀ p : Point, p.onLine DA → p ≠ f → ∠ p:f:e = ∟; assumption)) (by euclid_assumption "" (show a ≠ c; assumption)))
  have hafe : ∠ a:f:e = ∟ := hperp a haDA (Ne.symm step17_fa)
  have step17_pa : |(a─e)| * |(a─e)| = |(a─f)| * |(a─f)| + |(f─e)| * |(f─e)| := by euclid_apply (helper_3_36_step17_pa a e f DA EF (by euclid_assumption "" (show a.onLine DA; assumption)) (by euclid_assumption "" (show f.onLine DA; assumption)) (by euclid_assumption "" (show ¬ e.onLine DA; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show ∠ a:f:e = ∟; assumption)) (by euclid_assumption "" (show f ≠ a; assumption)))
  have step17_lt : |(e─f)| < |(e─a)| := by euclid_apply (helper_3_36_step17_lt a e f (by euclid_assumption "" (show |(a─e)| * |(a─e)| = |(a─f)| * |(a─f)| + |(f─e)| * |(f─e)|; assumption)) (by euclid_assumption "" (show f ≠ a; assumption)))
  have step17_bet : between a f c := by euclid_apply (helper_3_36_step17_bet a c e f ABC DA (by euclid_assumption "" (show a.onCircle ABC; assumption)) (by euclid_assumption "" (show c.onCircle ABC; assumption)) (by euclid_assumption "" (show a.onLine DA; assumption)) (by euclid_assumption "" (show c.onLine DA; assumption)) (by euclid_assumption "" (show f.onLine DA; assumption)) (by euclid_assumption "" (show e.isCentre ABC; assumption)) (by euclid_assumption "" (show a ≠ c; assumption)) (by euclid_assumption "" (show |(e─f)| < |(e─a)|; assumption)))
  have step17_p3 : |(a─f)| = |(f─c)| := by euclid_apply (helper_3_36_step17_p3 a c e f ABC DA EF (by euclid_assumption "" (show a.onCircle ABC; assumption)) (by euclid_assumption "" (show c.onCircle ABC; assumption)) (by euclid_assumption "" (show a.onLine DA; assumption)) (by euclid_assumption "" (show c.onLine DA; assumption)) (by euclid_assumption "" (show f.onLine DA; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show e.isCentre ABC; assumption)) (by euclid_assumption "" (show ¬ e.onLine DA; assumption)) (by euclid_assumption "" (show ∠ a:f:e = ∟; assumption)) (by euclid_assumption "" (show a ≠ c; assumption)) (by euclid_assumption "" (show between a f c; assumption)))
  exact step17_p3

end Elements.Book3

import SystemE
import Book3.Prop03.Main
import Book3.Prop36.step17_af
import Book3.Prop36.step17_cf
import Book3.Prop36.step17_feq
import Book3.Prop36.step17_bet
import Book3.Prop36.step17_perp
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step17
  (a c d e f : Point) (ABC : Circle) (DA EF : Line)
  (ha : a.onCircle ABC) (hc : c.onCircle ABC)
  (haDA : a.onLine DA) (hdDA : d.onLine DA)
  (hbet_dca : between d c a)
  (hfDA : f.onLine DA)
  (hperp : ∀ p : Point, p.onLine DA → p ≠ f → ∠ p:f:e = ∟)
  (heEF : e.onLine EF) (hfEF : f.onLine EF)
  (hassump1 : e.isCentre ABC ∧ e.onLine EF ∧ ¬e.onLine DA ∧ (∠ a:f:e = ∟ ∨ ∠ c:f:e = ∟))   -- "some straight-line, $EF$, through the center, cuts some (other) straight-line, $AC$, not through the center, at right-angles"
  : |(a─f)| = |(f─c)| := by
  obtain ⟨he, heEF', hnoteDA, hdisj⟩ := hassump1
  have step17_af : a ≠ f := by euclid_apply (helper_3_36_step17_af a c d e f ABC DA EF (by euclid_assumption "" (show a.onCircle ABC; assumption)) (by euclid_assumption "" (show c.onCircle ABC; assumption)) (by euclid_assumption "" (show a.onLine DA; assumption)) (by euclid_assumption "" (show d.onLine DA; assumption)) (by euclid_assumption "" (show between d c a; assumption)) (by euclid_assumption "" (show f.onLine DA; assumption)) (by euclid_assumption "" (show ∀ p : Point, p.onLine DA → p ≠ f → ∠ p:f:e = ∟; assumption)) (by euclid_assumption "" (show e.isCentre ABC; assumption)) (by euclid_assumption "" (show ¬e.onLine DA; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)))
  have step17_cf : c ≠ f := by euclid_apply (helper_3_36_step17_cf a c d e f ABC DA EF (by euclid_assumption "" (show a.onCircle ABC; assumption)) (by euclid_assumption "" (show c.onCircle ABC; assumption)) (by euclid_assumption "" (show a.onLine DA; assumption)) (by euclid_assumption "" (show d.onLine DA; assumption)) (by euclid_assumption "" (show between d c a; assumption)) (by euclid_assumption "" (show f.onLine DA; assumption)) (by euclid_assumption "" (show ∀ p : Point, p.onLine DA → p ≠ f → ∠ p:f:e = ∟; assumption)) (by euclid_assumption "" (show e.isCentre ABC; assumption)) (by euclid_assumption "" (show ¬e.onLine DA; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)))
  have step17_feq : |(f─a)| = |(f─c)| := by euclid_apply (helper_3_36_step17_feq a c d e f ABC DA EF (by euclid_assumption "" (show a.onCircle ABC; assumption)) (by euclid_assumption "" (show c.onCircle ABC; assumption)) (by euclid_assumption "" (show a.onLine DA; assumption)) (by euclid_assumption "" (show d.onLine DA; assumption)) (by euclid_assumption "" (show between d c a; assumption)) (by euclid_assumption "" (show f.onLine DA; assumption)) (by euclid_assumption "" (show ∀ p : Point, p.onLine DA → p ≠ f → ∠ p:f:e = ∟; assumption)) (by euclid_assumption "" (show e.isCentre ABC; assumption)) (by euclid_assumption "" (show ¬e.onLine DA; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show a ≠ f; assumption)) (by euclid_assumption "" (show c ≠ f; assumption)))
  have step17_bet : between a f c := by euclid_apply (helper_3_36_step17_bet a c d f DA (by euclid_assumption "" (show a.onLine DA; assumption)) (by euclid_assumption "" (show d.onLine DA; assumption)) (by euclid_assumption "" (show between d c a; assumption)) (by euclid_assumption "" (show f.onLine DA; assumption)) (by euclid_assumption "" (show a ≠ f; assumption)) (by euclid_assumption "" (show c ≠ f; assumption)) (by euclid_assumption "" (show |(f─a)| = |(f─c)|; assumption)))
  have step17_perp : ∠ a:f:e = ∟ := by euclid_apply (helper_3_36_step17_perp a e f DA (by euclid_assumption "" (show a.onLine DA; assumption)) (by euclid_assumption "" (show ∀ p : Point, p.onLine DA → p ≠ f → ∠ p:f:e = ∟; assumption)) (by euclid_assumption "" (show a ≠ f; assumption)))
  euclid_apply (Elements.Book3.proposition_3 a c e f ABC DA EF)
  euclid_finish

end Elements.Book3

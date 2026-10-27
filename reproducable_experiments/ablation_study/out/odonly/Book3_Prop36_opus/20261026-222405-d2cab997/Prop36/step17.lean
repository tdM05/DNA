import SystemE
import Book3.Prop03.Main
import Book3.Prop36.step17_anef
import Book3.Prop36.step17_fin
import Book3.Prop36.step17_btw
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step17 (a c d e f : Point) (ABC : Circle) (DA EF EC : Line)
  (hbdca : between d c a) (hada : a.onLine DA) (hdda : d.onLine DA)
  (hacirc : a.onCircle ABC) (hccirc : c.onCircle ABC)
  (hfDA : f.onLine DA) (hfEF : f.onLine EF)
  (heEC : e.onLine EC) (hcEC : c.onLine EC)
  (hperp_all : ∀ p : Point, p.onLine DA → p ≠ f → ∠ p:f:e = ∟)
  -- Reasoning hypotheses (from @assumption — keep these types in the signature):
  (hassump1 : e.isCentre ABC ∧ e.onLine EF ∧ ¬e.onLine DA ∧ (∠ a:f:e = ∟ ∨ ∠ c:f:e = ∟))   -- "some straight-line, $EF$, through the center, cuts some (other) straight-line, $AC$, not through the center, at right-angles"
  : |(a─f)| = |(f─c)| := by
  obtain ⟨hecentre, heEF, hennotDA, hangles⟩ := hassump1
  have hcda : c.onLine DA := by euclid_finish
  have hac : a ≠ c := by euclid_finish
  have step17_anef : a ≠ f := by euclid_apply (helper_3_36_step17_anef a c e f ABC DA EF EC (by euclid_assumption "" (show c.onLine DA; assumption)) (by euclid_assumption "" (show f.onLine DA; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show e.onLine EC; assumption)) (by euclid_assumption "" (show c.onLine EC; assumption)) (by euclid_assumption "" (show a.onCircle ABC; assumption)) (by euclid_assumption "" (show c.onCircle ABC; assumption)) (by euclid_assumption "" (show e.isCentre ABC; assumption)) (by euclid_assumption "" (show ¬ e.onLine DA; assumption)) (by euclid_assumption "" (show a ≠ c; assumption)) (by euclid_assumption "" (show ∀ p : Point, p.onLine DA → p ≠ f → ∠ p:f:e = ∟; assumption)))
  have hra : ∠ a:f:e = ∟ := hperp_all a hada step17_anef
  have step17_fin : f.insideCircle ABC := by euclid_apply (helper_3_36_step17_fin a e f ABC DA EF (by euclid_assumption "" (show a.onLine DA; assumption)) (by euclid_assumption "" (show f.onLine DA; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show a.onCircle ABC; assumption)) (by euclid_assumption "" (show e.isCentre ABC; assumption)) (by euclid_assumption "" (show ¬ e.onLine DA; assumption)) (by euclid_assumption "" (show a ≠ f; assumption)) (by euclid_assumption "" (show ∠ a:f:e = ∟; assumption)))
  have step17_btw : between a f c := by euclid_apply (helper_3_36_step17_btw a c f ABC DA (by euclid_assumption "" (show a.onLine DA; assumption)) (by euclid_assumption "" (show c.onLine DA; assumption)) (by euclid_assumption "" (show f.onLine DA; assumption)) (by euclid_assumption "" (show a.onCircle ABC; assumption)) (by euclid_assumption "" (show c.onCircle ABC; assumption)) (by euclid_assumption "" (show f.insideCircle ABC; assumption)) (by euclid_assumption "" (show a ≠ c; assumption)))
  have hperp : ∠ a:f:e = ∟ := hra
  euclid_apply (proposition_3 a c e f ABC DA EF)
  euclid_finish

end Elements.Book3

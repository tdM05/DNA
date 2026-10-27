import SystemE
import Book3.Prop03.Main
import Book3.Prop36.step17_dist
import Book3.Prop36.step17_in
import Book3.Prop36.step17_bet
import Book3.Prop36.step17_perp
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step17 (a c d e f : Point) (ABC : Circle) (DA EF : Line)
  (haC : a.onCircle ABC) (hcC : c.onCircle ABC)
  (haDA : a.onLine DA) (hdDA : d.onLine DA) (hfDA : f.onLine DA)
  (heEF : e.onLine EF) (hfEF : f.onLine EF)
  (hdca : between d c a)
  (hperpall : ∀ p : Point, p.onLine DA → p ≠ f → ∠ p:f:e = ∟)
  -- Reasoning hypotheses (from @assumption — keep these types in the signature):
  (hassump1 : e.isCentre ABC ∧ e.onLine EF ∧ ¬e.onLine DA ∧ (∠ a:f:e = ∟ ∨ ∠ c:f:e = ∟))   -- "some straight-line, $EF$, through the center, cuts some (other) straight-line, $AC$, not through the center, at right-angles"
  : |(a─f)| = |(f─c)| := by
  have step17_dist : distinctPointsOnLine a c DA := by euclid_apply (helper_3_36_step17_dist a c d DA (by euclid_assumption "" (show a.onLine DA; assumption)) (by euclid_assumption "" (show d.onLine DA; assumption)) (by euclid_assumption "" (show between d c a; assumption)))
  have step17_in : f.insideCircle ABC := by euclid_apply (helper_3_36_step17_in a c d e f ABC DA EF (by euclid_assumption "" (show a.onCircle ABC; assumption)) (by euclid_assumption "" (show c.onCircle ABC; assumption)) (by euclid_assumption "" (show a.onLine DA; assumption)) (by euclid_assumption "" (show d.onLine DA; assumption)) (by euclid_assumption "" (show f.onLine DA; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show between d c a; assumption)) (by euclid_assumption "" (show ∀ p : Point, p.onLine DA → p ≠ f → ∠ p:f:e = ∟; assumption)) (by euclid_assumption "" (show e.isCentre ABC ∧ e.onLine EF ∧ ¬e.onLine DA ∧ (∠ a:f:e = ∟ ∨ ∠ c:f:e = ∟); assumption)))
  have step17_bet : between a f c := by euclid_apply (helper_3_36_step17_bet a c d f ABC DA (by euclid_assumption "" (show a.onCircle ABC; assumption)) (by euclid_assumption "" (show c.onCircle ABC; assumption)) (by euclid_assumption "" (show a.onLine DA; assumption)) (by euclid_assumption "" (show d.onLine DA; assumption)) (by euclid_assumption "" (show f.onLine DA; assumption)) (by euclid_assumption "" (show between d c a; assumption)) (by euclid_assumption "" (show f.insideCircle ABC; assumption)))
  have step17_perp : ∠ a:f:e = ∟ := by euclid_apply (helper_3_36_step17_perp a c e f DA (by euclid_assumption "" (show a.onLine DA; assumption)) (by euclid_assumption "" (show ∀ p : Point, p.onLine DA → p ≠ f → ∠ p:f:e = ∟; assumption)) (by euclid_assumption "" (show between a f c; assumption)))
  euclid_apply (proposition_3 a c e f ABC DA EF
    ⟨haC, hcC, step17_dist, hassump1.1, heEF, hassump1.2.2.1, hfDA, hfEF, step17_bet⟩)
  euclid_finish

end Elements.Book3

import SystemE
import Book3.Prop03.Main
import Book3.Prop36.step17_btw
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step17 (a c d e f : Point) (ABC : Circle) (DA EF : Line)
  (ha_DA : a.onLine DA) (hd_DA : d.onLine DA) (hf_DA : f.onLine DA)
  (ha_circ : a.onCircle ABC) (hc_circ : c.onCircle ABC)
  (hbtw_dca : between d c a)
  (hf_EF : f.onLine EF)
  (hperp : ∀ (p : Point), p.onLine DA → p ≠ f → ∠ p:f:e = ∟)
  -- Reasoning hypotheses (from @assumption — keep these types in the signature):
  (hassump1 : e.isCentre ABC ∧ e.onLine EF ∧ ¬e.onLine DA ∧ (∠ a:f:e = ∟ ∨ ∠ c:f:e = ∟))   -- "some straight-line, $EF$, through the center, cuts some (other) straight-line, $AC$, not through the center, at right-angles"
  : |(a─f)| = |(f─c)| := by
  obtain ⟨he_centre, he_EF, hne_DA, hdisj⟩ := hassump1
  have hc_DA : c.onLine DA := by euclid_finish
  have hac : distinctPointsOnLine a c DA := by euclid_finish
  have step17_btw : between a f c := by euclid_apply (helper_3_36_step17_btw a c d e f ABC DA EF (by euclid_assumption "" (show a.onLine DA; assumption)) (by euclid_assumption "" (show c.onLine DA; assumption)) (by euclid_assumption "" (show f.onLine DA; assumption)) (by euclid_assumption "" (show a.onCircle ABC; assumption)) (by euclid_assumption "" (show c.onCircle ABC; assumption)) (by euclid_assumption "" (show between d c a; assumption)) (by euclid_assumption "" (show e.isCentre ABC; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show ¬ e.onLine DA; assumption)) (by euclid_assumption "" (show distinctPointsOnLine a c DA; assumption)) (by euclid_assumption "" (show ∀ (p : Point), p.onLine DA → p ≠ f → ∠ p:f:e = ∟; assumption)))
  rcases hdisj with hang | hang
  · euclid_apply (proposition_3 a c e f ABC DA EF (by euclid_finish)).2 hang
  · euclid_apply (proposition_3 c a e f ABC DA EF (by euclid_finish)).2 hang
    euclid_finish

end Elements.Book3

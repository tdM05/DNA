import SystemE
import Book3.Prop03.Main
import Book3.Prop36.step17_bet
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step17
  (a c d e f : Point) (ABC : Circle) (DA EF : Line)
  (ha_circ : a.onCircle ABC) (hc_circ : c.onCircle ABC)
  (ha_DA : a.onLine DA) (hd_DA : d.onLine DA) (hf_DA : f.onLine DA)
  (he_EF : e.onLine EF) (hf_EF : f.onLine EF)
  (hbet : between d c a)
  (hperp_all : ∀ p : Point, p.onLine DA → p ≠ f → ∠ p:f:e = ∟)
  -- Reasoning hypotheses (from @assumption — keep these types in the signature):
  (hassump1 : e.isCentre ABC ∧ e.onLine EF ∧ ¬e.onLine DA ∧ (∠ a:f:e = ∟ ∨ ∠ c:f:e = ∟))   -- "some straight-line, $EF$, through the center, cuts some (other) straight-line, $AC$, not through the center, at right-angles"
  : |(a─f)| = |(f─c)| := by
  have step17_bet : between a f c := by euclid_apply (helper_3_36_step17_bet a c d e f ABC DA EF (by euclid_assumption "" (show a.onCircle ABC; assumption)) (by euclid_assumption "" (show c.onCircle ABC; assumption)) (by euclid_assumption "" (show a.onLine DA; assumption)) (by euclid_assumption "" (show d.onLine DA; assumption)) (by euclid_assumption "" (show f.onLine DA; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show between d c a; assumption)) (by euclid_assumption "" (show ∀ p : Point, p.onLine DA → p ≠ f → ∠ p:f:e = ∟; assumption)) (by euclid_assumption "" (show e.isCentre ABC ∧ e.onLine EF ∧ ¬e.onLine DA ∧ (∠ a:f:e = ∟ ∨ ∠ c:f:e = ∟); assumption)))
  euclid_apply (Elements.Book3.proposition_3 a c e f ABC DA EF)
  euclid_finish

end Elements.Book3

import SystemE
import Mathlib.Tactic.Linarith
import Book3.Prop36.step17_btw_fne
import Book3.Prop36.step17_btw_pyth
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step17_btw (a c d e f : Point) (ABC : Circle) (DA EF : Line)
  (ha_DA : a.onLine DA) (hc_DA : c.onLine DA) (hf_DA : f.onLine DA)
  (ha_circ : a.onCircle ABC) (hc_circ : c.onCircle ABC)
  (hbtw_dca : between d c a)
  (he_centre : e.isCentre ABC) (he_EF : e.onLine EF) (hf_EF : f.onLine EF)
  (hne_DA : ¬ e.onLine DA)
  (hac : distinctPointsOnLine a c DA)
  (hperp : ∀ (p : Point), p.onLine DA → p ≠ f → ∠ p:f:e = ∟)
  : between a f c := by
  have step17_btw_fne : f ≠ a := by euclid_apply (helper_3_36_step17_btw_fne a c e f ABC DA EF (by euclid_assumption "" (show a.onLine DA; assumption)) (by euclid_assumption "" (show c.onLine DA; assumption)) (by euclid_assumption "" (show f.onLine DA; assumption)) (by euclid_assumption "" (show a.onCircle ABC; assumption)) (by euclid_assumption "" (show c.onCircle ABC; assumption)) (by euclid_assumption "" (show e.isCentre ABC; assumption)) (by euclid_assumption "" (show ¬ e.onLine DA; assumption)) (by euclid_assumption "" (show distinctPointsOnLine a c DA; assumption)) (by euclid_assumption "" (show ∀ (p : Point), p.onLine DA → p ≠ f → ∠ p:f:e = ∟; assumption)))
  have step17_btw_pyth : |(e─a)| * |(e─a)| = |(e─f)| * |(e─f)| + |(f─a)| * |(f─a)| := by euclid_apply (helper_3_36_step17_btw_pyth a e f ABC DA EF (by euclid_assumption "" (show a.onLine DA; assumption)) (by euclid_assumption "" (show f.onLine DA; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show ¬ e.onLine DA; assumption)) (by euclid_assumption "" (show f ≠ a; assumption)) (by euclid_assumption "" (show ∀ (p : Point), p.onLine DA → p ≠ f → ∠ p:f:e = ∟; assumption)))
  have hfa_pos : (0:ℝ) < |(f─a)| := by euclid_finish
  have hea_nn : (0:ℝ) ≤ |(e─a)| := by euclid_finish
  have hef_nn : (0:ℝ) ≤ |(e─f)| := by euclid_finish
  have hlt : |(e─f)| < |(e─a)| := by nlinarith [step17_btw_pyth, hfa_pos, hea_nn, hef_nn, mul_pos hfa_pos hfa_pos]
  have hf_inside : f.insideCircle ABC := by euclid_finish
  euclid_apply (circle_line_intersections f a c DA ABC (by euclid_finish))

end Elements.Book3

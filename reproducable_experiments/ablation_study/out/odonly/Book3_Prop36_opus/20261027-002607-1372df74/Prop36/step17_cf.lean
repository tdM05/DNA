import SystemE
import Book1.Prop47.Main
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1

theorem helper_3_36_step17_cf
  (a c d e f : Point) (ABC : Circle) (DA EF : Line)
  (ha : a.onCircle ABC) (hc : c.onCircle ABC)
  (haDA : a.onLine DA) (hdDA : d.onLine DA)
  (hbet_dca : between d c a)
  (hfDA : f.onLine DA)
  (hperp : ∀ p : Point, p.onLine DA → p ≠ f → ∠ p:f:e = ∟)
  (he : e.isCentre ABC) (hnoteDA : ¬e.onLine DA)
  (heEF : e.onLine EF) (hfEF : f.onLine EF)
  : c ≠ f := by
  intro hcf
  have hac : a ≠ c := by euclid_finish
  have haf : a ≠ f := by rw [← hcf]; exact hac
  have hperpa : ∠ a:f:e = ∟ := hperp a haDA haf
  euclid_apply (line_from_points e a) as EA
  euclid_apply (Elements.Book1.proposition_47 f e a EF EA DA)
  -- now |(e─a)|*|(e─a)| = |(e─f)|*|(e─f)| + |(f─a)|*|(f─a)| is in context
  have hrad : |(e─f)| = |(e─a)| := by rw [← hcf]; euclid_finish
  have hrad2 : |(e─f)| * |(e─f)| = |(e─a)| * |(e─a)| := by rw [hrad]
  have key : |(f─a)| * |(f─a)| = 0 := by linarith
  have hfa0 : |(f─a)| = 0 := by
    rcases mul_eq_zero.mp key with h | h <;> exact h
  exact haf (zero_segment_if f a hfa0).symm

end Elements.Book3

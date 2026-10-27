import SystemE
import Book1.Prop47.Main
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1

theorem helper_3_36_step17_af
  (a c d e f : Point) (ABC : Circle) (DA EF : Line)
  (ha : a.onCircle ABC) (hc : c.onCircle ABC)
  (haDA : a.onLine DA) (hdDA : d.onLine DA)
  (hbet_dca : between d c a)
  (hfDA : f.onLine DA)
  (hperp : ∀ p : Point, p.onLine DA → p ≠ f → ∠ p:f:e = ∟)
  (he : e.isCentre ABC) (hnoteDA : ¬e.onLine DA)
  (heEF : e.onLine EF) (hfEF : f.onLine EF)
  : a ≠ f := by
  intro haf
  have hac : a ≠ c := by euclid_finish
  have hcDA : c.onLine DA := by euclid_finish
  have hcf : c ≠ f := by rw [← haf]; exact fun h => hac h.symm
  have hperpc : ∠ c:f:e = ∟ := hperp c hcDA hcf
  euclid_apply (line_from_points e c) as EC
  euclid_apply (Elements.Book1.proposition_47 f e c EF EC DA)
  -- now |(e─c)|*|(e─c)| = |(e─f)|*|(e─f)| + |(f─c)|*|(f─c)| is in context
  have hrad : |(e─f)| = |(e─c)| := by rw [← haf]; euclid_finish
  have hrad2 : |(e─f)| * |(e─f)| = |(e─c)| * |(e─c)| := by rw [hrad]
  have key : |(f─c)| * |(f─c)| = 0 := by linarith
  have hfc0 : |(f─c)| = 0 := by
    rcases mul_eq_zero.mp key with h | h <;> exact h
  exact hcf (zero_segment_if f c hfc0).symm

end Elements.Book3

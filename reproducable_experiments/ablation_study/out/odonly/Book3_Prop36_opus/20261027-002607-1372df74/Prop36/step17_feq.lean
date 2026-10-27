import SystemE
import Book1.Prop47.Main
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1

theorem helper_3_36_step17_feq
  (a c d e f : Point) (ABC : Circle) (DA EF : Line)
  (ha : a.onCircle ABC) (hc : c.onCircle ABC)
  (haDA : a.onLine DA) (hdDA : d.onLine DA)
  (hbet_dca : between d c a)
  (hfDA : f.onLine DA)
  (hperp : ∀ p : Point, p.onLine DA → p ≠ f → ∠ p:f:e = ∟)
  (he : e.isCentre ABC) (hnoteDA : ¬e.onLine DA)
  (heEF : e.onLine EF) (hfEF : f.onLine EF)
  (step17_af : a ≠ f) (step17_cf : c ≠ f)
  : |(f─a)| = |(f─c)| := by
  have hcDA : c.onLine DA := by euclid_finish
  have hperpa : ∠ a:f:e = ∟ := hperp a haDA step17_af
  have hperpc : ∠ c:f:e = ∟ := hperp c hcDA step17_cf
  euclid_apply (line_from_points e a) as EA
  euclid_apply (line_from_points e c) as EC
  euclid_apply (Elements.Book1.proposition_47 f e a EF EA DA)
  euclid_apply (Elements.Book1.proposition_47 f e c EF EC DA)
  have hrad : |(e─a)| = |(e─c)| := by euclid_finish
  have hrad2 : |(e─a)| * |(e─a)| = |(e─c)| * |(e─c)| := by rw [hrad]
  have hsq : |(f─a)| * |(f─a)| = |(f─c)| * |(f─c)| := by linarith
  have hfa_nn : 0 ≤ |(f─a)| := segment_gte_zero _
  have hfc_nn : 0 ≤ |(f─c)| := segment_gte_zero _
  nlinarith [hsq, hfa_nn, hfc_nn, mul_self_nonneg (|(f─a)| - |(f─c)|)]

end Elements.Book3

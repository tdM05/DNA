import SystemE
import Book1.Prop47.Main
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step17_btw_fne (a c e f : Point) (ABC : Circle) (DA EF : Line)
  (ha_DA : a.onLine DA) (hc_DA : c.onLine DA) (hf_DA : f.onLine DA)
  (ha_circ : a.onCircle ABC) (hc_circ : c.onCircle ABC)
  (he_centre : e.isCentre ABC) (hne_DA : ¬ e.onLine DA)
  (hac : distinctPointsOnLine a c DA)
  (hperp : ∀ (p : Point), p.onLine DA → p ≠ f → ∠ p:f:e = ∟)
  : f ≠ a := by
  intro hfa
  have hcf : c ≠ f := by euclid_finish
  have hcfe : ∠ c:f:e = ∟ := hperp c hc_DA hcf
  rw [hfa] at hcfe
  have hang : ∠ e:a:c = ∟ := by euclid_finish
  euclid_apply (line_from_points e a) as EA
  euclid_apply (line_from_points e c) as EC
  have htri : formTriangle a e c EA EC DA := by euclid_finish
  euclid_apply (Elements.Book1.proposition_47 a e c EA EC DA ⟨htri, hang⟩)
  have hac_pos : (0:ℝ) < |(a─c)| := by euclid_finish
  have hrad2 : |(e─a)| * |(e─a)| = |(e─c)| * |(e─c)| := by
    have hrad : |(e─a)| = |(e─c)| := by euclid_finish
    rw [hrad]
  linarith [hrad2, mul_pos hac_pos hac_pos]

end Elements.Book3

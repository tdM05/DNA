import SystemE
import Book1.Prop47.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step17_af
  (a c d e f : Point) (ABC : Circle) (DA EF : Line)
  (ha_circ : a.onCircle ABC) (hc_circ : c.onCircle ABC)
  (ha_DA : a.onLine DA) (hd_DA : d.onLine DA) (hf_DA : f.onLine DA)
  (he_EF : e.onLine EF) (hf_EF : f.onLine EF)
  (hbet : between d c a)
  (hperp_all : ∀ p : Point, p.onLine DA → p ≠ f → ∠ p:f:e = ∟)
  (hecenter : e.isCentre ABC) (hnotDA : ¬ e.onLine DA)
  : a ≠ f := by
  rintro rfl
  -- a = f. Then c (the OTHER intersection, c ≠ a) is on AC and distinct from f, so the
  -- perpendicular gives ∠c:f:e = ∟; right triangle e-f-c forces |e─c| > |e─f| = radius = |e─c|.
  have hcf : c ≠ a := by euclid_finish
  have hc_DA : c.onLine DA := by euclid_finish
  have hperp_c : ∠ c:a:e = ∟ := hperp_all c hc_DA hcf
  euclid_apply (line_from_points e c) as EC
  euclid_apply (Elements.Book1.proposition_47 a e c EF EC DA)
  euclid_finish

end Elements.Book3

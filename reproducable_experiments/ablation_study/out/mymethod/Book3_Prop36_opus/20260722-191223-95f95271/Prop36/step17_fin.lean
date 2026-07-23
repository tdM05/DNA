import SystemE
import Book1.Prop47.Main
import Book3.Prop36.step17_af
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step17_fin
  (a c d e f : Point) (ABC : Circle) (DA EF : Line)
  (ha_circ : a.onCircle ABC) (hc_circ : c.onCircle ABC)
  (ha_DA : a.onLine DA) (hd_DA : d.onLine DA) (hf_DA : f.onLine DA)
  (he_EF : e.onLine EF) (hf_EF : f.onLine EF)
  (hbet : between d c a)
  (hperp_all : ∀ p : Point, p.onLine DA → p ≠ f → ∠ p:f:e = ∟)
  (hassump1 : e.isCentre ABC ∧ e.onLine EF ∧ ¬e.onLine DA ∧ (∠ a:f:e = ∟ ∨ ∠ c:f:e = ∟))
  : f.insideCircle ABC := by
  obtain ⟨hecenter, he_EF2, hnotDA, hperp⟩ := hassump1
  have step17_af : a ≠ f := by euclid_apply (helper_3_36_step17_af a c d e f ABC DA EF (by euclid_assumption "" (show a.onCircle ABC; assumption)) (by euclid_assumption "" (show c.onCircle ABC; assumption)) (by euclid_assumption "" (show a.onLine DA; assumption)) (by euclid_assumption "" (show d.onLine DA; assumption)) (by euclid_assumption "" (show f.onLine DA; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show between d c a; assumption)) (by euclid_assumption "" (show ∀ p : Point, p.onLine DA → p ≠ f → ∠ p:f:e = ∟; assumption)) (by euclid_assumption "" (show e.isCentre ABC; assumption)) (by euclid_assumption "" (show ¬ e.onLine DA; assumption)))
  -- the perpendicular from e meets AC at f at a right angle; a is a point of AC distinct from f
  have hperp_a : ∠ a:f:e = ∟ := hperp_all a ha_DA step17_af
  -- right triangle e-f-a: |e─a|² = |e─f|² + |f─a|², so |e─f| < |e─a| = radius ⟹ f inside
  euclid_apply (line_from_points e a) as EA
  euclid_apply (Elements.Book1.proposition_47 f e a EF EA DA)
  euclid_finish

end Elements.Book3

import SystemE
import Book1.Prop47.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step17_btw_pyth (a e f : Point) (ABC : Circle) (DA EF : Line)
  (ha_DA : a.onLine DA) (hf_DA : f.onLine DA)
  (he_EF : e.onLine EF) (hf_EF : f.onLine EF)
  (hne_DA : ¬ e.onLine DA)
  (hfa : f ≠ a)
  (hperp : ∀ (p : Point), p.onLine DA → p ≠ f → ∠ p:f:e = ∟)
  : |(e─a)| * |(e─a)| = |(e─f)| * |(e─f)| + |(f─a)| * |(f─a)| := by
  have haf : a ≠ f := fun h => hfa h.symm
  have hafe : ∠ a:f:e = ∟ := hperp a ha_DA haf
  have hang : ∠ e:f:a = ∟ := by euclid_finish
  euclid_apply (line_from_points e a) as EA
  have htri : formTriangle f e a EF EA DA := by euclid_finish
  euclid_apply (Elements.Book1.proposition_47 f e a EF EA DA ⟨htri, hang⟩)

end Elements.Book3

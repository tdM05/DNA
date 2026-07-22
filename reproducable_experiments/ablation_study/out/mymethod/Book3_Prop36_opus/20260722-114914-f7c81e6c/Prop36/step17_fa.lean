import SystemE
import Book1.Prop47.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1

theorem helper_3_36_step17_fa
  (a c e f : Point) (ABC : Circle) (DA : Line)
  (ha : a.onCircle ABC) (hc : c.onCircle ABC)
  (hcentre : e.isCentre ABC)
  (haDA : a.onLine DA) (hcDA : c.onLine DA) (hfDA : f.onLine DA)
  (hnotDA : ¬ e.onLine DA)
  (hperp : ∀ p : Point, p.onLine DA → p ≠ f → ∠ p:f:e = ∟)
  (hac : a ≠ c)
  : f ≠ a := by
  intro hfa
  subst hfa
  have hcfe : ∠ c:f:e = ∟ := hperp c hcDA (Ne.symm hac)
  euclid_apply (line_from_points e f) as EA
  euclid_apply (line_from_points e c) as EC
  have htri : formTriangle f c e DA EC EA := by euclid_finish
  euclid_apply (Elements.Book1.proposition_47 f c e DA EC EA)
  euclid_finish

end Elements.Book3

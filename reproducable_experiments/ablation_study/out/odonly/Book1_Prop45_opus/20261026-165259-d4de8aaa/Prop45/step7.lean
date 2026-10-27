import SystemE
import Book1Variants.Prop29

namespace Elements.Book1

set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

theorem helper_1_45_step7 (f g k h : Point) (FG KH FK GH : Line)
  (hfFG : f.onLine FG) (hgFG : g.onLine FG)
  (hkKH : k.onLine KH) (hhKH : h.onLine KH)
  (hfFK : f.onLine FK) (hkFK : k.onLine FK)
  (hgGH : g.onLine GH) (hhGH : h.onLine GH) (hgh : g ≠ h)
  (hsame : f.sameSide k GH)
  (hni1 : ¬FG.intersectsLine KH) (hni2 : ¬FK.intersectsLine GH)
  : ∠ f:k:h + ∠ k:h:g = ∟ + ∟ := by
  euclid_apply (proposition_29''''' f g k h FK GH KH)
  euclid_finish

end Elements.Book1

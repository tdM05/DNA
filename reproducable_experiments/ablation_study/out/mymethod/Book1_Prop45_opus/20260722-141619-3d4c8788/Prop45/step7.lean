import SystemE
import Book1Variants.Prop29

set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step7 (f g h k : Point) (FG KH FK GH : Line)
    (h1 : f.onLine FG) (h2 : g.onLine FG)
    (h3 : k.onLine KH) (h4 : h.onLine KH)
    (h5 : f.onLine FK) (h6 : k.onLine FK)
    (h7 : g.onLine GH) (h8 : h.onLine GH) (h9 : g ≠ h)
    (h10 : f.sameSide k GH)
    (h11 : ¬FG.intersectsLine KH) (h12 : ¬FK.intersectsLine GH)
    (hkGH : ¬k.onLine GH)
    : ∠ f:k:h + ∠ k:h:g = ∟ + ∟ := by
  euclid_apply (parallelogram_same_side f g k h FG KH FK GH)
  euclid_apply (proposition_29''''' f g k h FK GH KH)
  euclid_finish

end Elements.Book1

import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step6 (f g h k m : Point) (FG KH FK GH : Line)
    (h1 : f.onLine FG) (h2 : g.onLine FG)
    (h3 : k.onLine KH) (h4 : h.onLine KH)
    (h5 : f.onLine FK) (h6 : k.onLine FK)
    (h7 : g.onLine GH) (h8 : h.onLine GH) (h9 : g ≠ h)
    (h10 : f.sameSide k GH)
    (h11 : ¬FG.intersectsLine KH) (h12 : ¬FK.intersectsLine GH)
    (hkGH : ¬k.onLine GH)
    (hstep5 : ∠ h:k:f + ∠ k:h:g = ∠ g:h:m + ∠ k:h:g)
    : ∠ f:k:h + ∠ k:h:g = ∠ k:h:g + ∠ g:h:m := by
  euclid_apply (parallelogram_same_side f g k h FG KH FK GH)
  euclid_apply (angle_symm f k h)
  linarith [hstep5]

end Elements.Book1

import SystemE
import Book1Variants.Prop29
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step7
  (f g h k : Point) (FG KH FK GH : Line)
  (hf_FG : f.onLine FG) (hg_FG : g.onLine FG)
  (hk_KH : k.onLine KH) (hh_KH : h.onLine KH)
  (hf_FK : f.onLine FK) (hk_FK : k.onLine FK)
  (hg_GH : g.onLine GH) (hh_GH : h.onLine GH) (hgh : g ≠ h)
  (hfk_GH : f.sameSide k GH)
  (hFGKH : ¬FG.intersectsLine KH) (hFKGH : ¬FK.intersectsLine GH) :
  ∠ f:k:h + ∠ k:h:g = ∟ + ∟ := by
  euclid_apply (proposition_29''''' f g k h FK GH KH)
  euclid_finish

end Elements.Book1

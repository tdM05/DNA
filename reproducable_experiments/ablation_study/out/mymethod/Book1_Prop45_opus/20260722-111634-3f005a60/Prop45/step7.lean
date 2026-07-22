import SystemE
import Book1Variants.Prop29
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step7 (f g h k : Point) (FG KH FK GH : Line)
    (hfFG : f.onLine FG) (hgFG : g.onLine FG) (hkKH : k.onLine KH) (hhKH : h.onLine KH)
    (hfFK : f.onLine FK) (hkFK : k.onLine FK) (hgGH : g.onLine GH) (hhGH : h.onLine GH)
    (hss : f.sameSide k GH) (hgh : g ≠ h) (hkGH : ¬ k.onLine GH)
    (hpar1 : ¬FG.intersectsLine KH) (hpar2 : ¬FK.intersectsLine GH) :
    ∠ f:k:h + ∠ k:h:g = ∟ + ∟ := by
  have hkf : k ≠ f := by euclid_finish
  have hkh : k ≠ h := by euclid_finish
  have hfg_ss : f.sameSide g KH := by euclid_finish
  euclid_apply (proposition_29''''' f g k h FK GH KH)
  euclid_finish

end Elements.Book1

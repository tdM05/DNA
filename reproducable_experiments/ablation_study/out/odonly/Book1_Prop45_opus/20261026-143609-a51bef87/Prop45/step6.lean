import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step6 (f g h k m : Point) (FG KH FK GH : Line)
    (hstep5 : ∠ h:k:f + ∠ k:h:g = ∠ g:h:m + ∠ k:h:g)
    (hf_FG : f.onLine FG) (hg_FG : g.onLine FG)
    (hk_KH : k.onLine KH) (hh_KH : h.onLine KH)
    (hf_FK : f.onLine FK) (hk_FK : k.onLine FK)
    (hg_GH : g.onLine GH) (hh_GH : h.onLine GH) (hgh_ne : g ≠ h)
    (hss : f.sameSide k GH)
    (hni1 : ¬(FG.intersectsLine KH)) (hni2 : ¬(FK.intersectsLine GH)) :
    ∠ f:k:h + ∠ k:h:g = ∠ k:h:g + ∠ g:h:m := by
  have hfk : f ≠ k := by euclid_finish
  have hkh : k ≠ h := by euclid_finish
  have hsym : ∠ f:k:h = ∠ h:k:f := angle_symm f k h ⟨hfk, hkh⟩
  linarith [hstep5, hsym]

end Elements.Book1

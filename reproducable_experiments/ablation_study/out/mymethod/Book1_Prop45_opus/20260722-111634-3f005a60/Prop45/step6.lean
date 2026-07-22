import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step6 (f g h k m : Point) (FG KH GH : Line)
    (hstep5 : ∠ h:k:f + ∠ k:h:g = ∠ g:h:m + ∠ k:h:g)
    (hfFG : f.onLine FG) (hgFG : g.onLine FG) (hkKH : k.onLine KH) (hhKH : h.onLine KH)
    (hgGH : g.onLine GH) (hhGH : h.onLine GH) (hgh : g ≠ h)
    (hss : f.sameSide k GH) (hpar : ¬FG.intersectsLine KH) (hkGH : ¬k.onLine GH) :
    ∠ f:k:h + ∠ k:h:g = ∠ k:h:g + ∠ g:h:m := by
  have hkh : k ≠ h := by euclid_finish
  have hfk : f ≠ k := by euclid_finish
  have hsymm : ∠ f:k:h = ∠ h:k:f := angle_symm f k h ⟨hfk, hkh⟩
  rw [hsymm]
  linarith [hstep5]

end Elements.Book1

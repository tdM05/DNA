import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step6 (f g h k m : Point) (FG KH GH : Line)
  (hstep5 : ∠ h:k:f + ∠ k:h:g = ∠ g:h:m + ∠ k:h:g)
  (hfFG : f.onLine FG) (hgFG : g.onLine FG)
  (hkKH : k.onLine KH) (hhKH : h.onLine KH)
  (hgGH : g.onLine GH) (hhGH : h.onLine GH) (hgh : g ≠ h)
  (hsame : f.sameSide k GH) (hni1 : ¬FG.intersectsLine KH)
  : ∠ f:k:h + ∠ k:h:g = ∠ k:h:g + ∠ g:h:m := by
  have hfk : f ≠ k := by euclid_finish
  have hkh : k ≠ h := by euclid_finish
  have hsymm : ∠ f:k:h = ∠ h:k:f := angle_symm f k h ⟨hfk, hkh⟩
  euclid_finish

end Elements.Book1

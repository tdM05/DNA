import SystemE
import Book1.Prop45.step21_bkhm
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_hangle (e₁ e₂ e₃ f g h k m : Point) (FG KH HM FK GH : Line)
  (hang : ∠ h:k:f = ∠ e₁:e₂:e₃)
  (hfFG : f.onLine FG) (hgFG : g.onLine FG)
  (hfFK : f.onLine FK) (hkFK : k.onLine FK)
  (hhKH : h.onLine KH) (hkKH : k.onLine KH) (hmHM : m.onLine HM) (hstep10 : KH = HM)
  (hgGH : g.onLine GH) (hhGH : h.onLine GH) (hgh : g ≠ h)
  (hsame : f.sameSide k GH) (hniFGKH : ¬FG.intersectsLine KH)
  (hstep9 : k.opposingSides m GH ∧ (∠ k:h:g + ∠ g:h:m = ∟ + ∟))
  : ∠ f:k:m = ∠ e₁:e₂:e₃ := by
  obtain ⟨hopp, _⟩ := hstep9
  have step21_bkhm : between k h m := by euclid_apply (helper_1_45_step21_bkhm g h k m KH HM GH (by euclid_assumption "" (show k.opposingSides m GH; assumption)) (by euclid_assumption "" (show h.onLine GH; assumption)) (by euclid_assumption "" (show k.onLine KH; assumption)) (by euclid_assumption "" (show h.onLine KH; assumption)) (by euclid_assumption "" (show m.onLine HM; assumption)) (by euclid_assumption "" (show KH = HM; assumption)))
  have hfk : f ≠ k := by euclid_finish
  have hkh : k ≠ h := by euclid_finish
  have hmk : m ≠ k := by euclid_finish
  euclid_apply (equal_angles k f f h m FK KH)
  euclid_finish

end Elements.Book1

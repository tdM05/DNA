import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_hangle
  (e₁ e₂ e₃ f g h k m : Point) (KH HM GH FG FK : Line)
  (hk_KH : k.onLine KH) (hh_KH : h.onLine KH) (hm_HM : m.onLine HM)
  (hh_GH : h.onLine GH)
  (hf_FK : f.onLine FK) (hk_FK : k.onLine FK)
  (hf_FG : f.onLine FG) (hg_FG : g.onLine FG) (hg_GH : g.onLine GH) (hgh : g ≠ h)
  (hfk_ss : f.sameSide k GH) (hFGKH : ¬FG.intersectsLine KH)
  (step9 : k.opposingSides m GH ∧ (∠ k:h:g + ∠ g:h:m = ∟ + ∟))
  (step10 : KH = HM)
  (hangle_hkf : ∠ h:k:f = ∠ e₁:e₂:e₃) :
  ∠ f:k:m = ∠ e₁:e₂:e₃ := by
  have hm_KH : m.onLine KH := by rw [step10]; exact hm_HM
  have hbet : between k h m := by euclid_finish
  have hFGKH_ne : FG ≠ KH := by euclid_finish
  have hfk_ne : f ≠ k := by euclid_finish
  have hswap : ∠ f:k:m = ∠ f:k:h := by
    euclid_apply (equal_angles k f f m h FK KH)
    euclid_finish
  euclid_finish

end Elements.Book1

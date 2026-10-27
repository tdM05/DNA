import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_hangle (e₁ e₂ e₃ f g h k m : Point) (KH HM GH FK FG : Line)
    (hk_KH : k.onLine KH) (hh_KH : h.onLine KH) (hm_HM : m.onLine HM) (step10 : KH = HM)
    (hf_FK : f.onLine FK) (hk_FK : k.onLine FK)
    (hf_FG : f.onLine FG) (hg_FG : g.onLine FG) (hFGKH : ¬FG.intersectsLine KH)
    (hg_GH : g.onLine GH) (hh_GH : h.onLine GH) (hgh : g ≠ h)
    (hk_offGH : ¬k.onLine GH) (hm_offGH : ¬m.onLine GH) (hmk_ns : ¬m.sameSide k GH)
    (hang : ∠ h:k:f = ∠ e₁:e₂:e₃) :
    ∠ f:k:m = ∠ e₁:e₂:e₃ := by
  have hmKH : m.onLine KH := by rw [step10]; exact hm_HM
  have hFGKH_ne : FG ≠ KH := by euclid_finish
  have hfk_ne : f ≠ k := by euclid_finish
  have hbkhm : between k h m := by
    euclid_apply (between_points k h m KH)
    euclid_finish
  euclid_apply (equal_angles k h m f f KH FK)
  euclid_finish

end Elements.Book1

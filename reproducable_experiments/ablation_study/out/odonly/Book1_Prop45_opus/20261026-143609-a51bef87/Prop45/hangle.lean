import SystemE
import Book1.Prop45.hangle_bkm
import Book1.Prop45.hangle_eq
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_hangle (e₁ e₂ e₃ f g h k l m : Point) (FG KH FK GH : Line)
    (hangle_E : ∠ h:k:f = ∠ e₁:e₂:e₃)
    (hstep18 : distinctPointsOnLine k m KH ∧ distinctPointsOnLine f l FG)
    (hf_FK : f.onLine FK) (hk_FK : k.onLine FK)
    (hh_KH : h.onLine KH) (hh_GH : h.onLine GH)
    (hg_FG : g.onLine FG) (hg_GH : g.onLine GH) (hgh_ne : g ≠ h)
    (hk_notGH : ¬(k.onLine GH)) (hm_notGH : ¬(m.onLine GH)) (hmk_ss : ¬(m.sameSide k GH))
    (hni_FGKH : ¬(FG.intersectsLine KH)) :
    ∠ f:k:m = ∠ e₁:e₂:e₃ := by
  obtain ⟨⟨hk_KH, hm_KH, hkm_ne⟩, ⟨hf_FG, hl_FG, hfl_ne⟩⟩ := hstep18
  have hangle_bkm : between k h m := by euclid_apply (helper_1_45_hangle_bkm h k m GH KH (by euclid_assumption "" (show h.onLine GH; assumption)) (by euclid_assumption "" (show h.onLine KH; assumption)) (by euclid_assumption "" (show k.onLine KH; assumption)) (by euclid_assumption "" (show m.onLine KH; assumption)) (by euclid_assumption "" (show ¬(k.onLine GH); assumption)) (by euclid_assumption "" (show ¬(m.onLine GH); assumption)) (by euclid_assumption "" (show ¬(m.sameSide k GH); assumption)))
  have hangle_eq : ∠ f:k:m = ∠ f:k:h := by euclid_apply (helper_1_45_hangle_eq f g h k m FG KH FK GH (by euclid_assumption "" (show f.onLine FK; assumption)) (by euclid_assumption "" (show k.onLine FK; assumption)) (by euclid_assumption "" (show k.onLine KH; assumption)) (by euclid_assumption "" (show m.onLine KH; assumption)) (by euclid_assumption "" (show h.onLine KH; assumption)) (by euclid_assumption "" (show f.onLine FG; assumption)) (by euclid_assumption "" (show g.onLine FG; assumption)) (by euclid_assumption "" (show g.onLine GH; assumption)) (by euclid_assumption "" (show h.onLine GH; assumption)) (by euclid_assumption "" (show ¬(k.onLine GH); assumption)) (by euclid_assumption "" (show g ≠ h; assumption)) (by euclid_assumption "" (show ¬(FG.intersectsLine KH); assumption)) (by euclid_assumption "" (show between k h m; assumption)))
  euclid_finish

end Elements.Book1

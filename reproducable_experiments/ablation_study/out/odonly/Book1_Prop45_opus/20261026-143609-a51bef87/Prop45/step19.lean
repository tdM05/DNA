import SystemE
import Book1.Prop33.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step19 (f g h k l m : Point) (FG KH FK LM GH : Line)
    (hstep17 : |(k─f)| = |(m─l)| ∧ ¬(FK.intersectsLine LM))
    (hstep18 : distinctPointsOnLine k m KH ∧ distinctPointsOnLine f l FG)
    (hk_FK : k.onLine FK) (hf_FK : f.onLine FK)
    (hm_LM : m.onLine LM) (hl_LM : l.onLine LM) (hml_ne : m ≠ l)
    (hf_FG : f.onLine FG) (hk_KH : k.onLine KH)
    (hg_FG : g.onLine FG) (hg_GH : g.onLine GH) (hh_GH : h.onLine GH)
    (hh_KH : h.onLine KH) (hk_notGH : ¬(k.onLine GH)) (hgh_ne : g ≠ h)
    (hni_FGKH : ¬(FG.intersectsLine KH)) :
    |(k─m)| = |(f─l)| ∧ ¬(KH.intersectsLine FG) := by
  obtain ⟨hd_km, hd_fl⟩ := hstep18
  have hm_KH : m.onLine KH := hd_km.2.1
  have hgKH : ¬ g.onLine KH := by euclid_finish
  have hFGKH : FG ≠ KH := by euclid_finish
  have hk_nFG : ¬ k.onLine FG := by euclid_finish
  have hm_nFG : ¬ m.onLine FG := by euclid_finish
  have hkm_FG : k.sameSide m FG := by euclid_finish
  euclid_apply (proposition_33 k f m l FK LM KH FG)
  euclid_finish

end Elements.Book1

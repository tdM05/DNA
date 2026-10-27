import SystemE
import Book1.Prop33.Main
import Book1.Prop45.step19_kmss
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step19 (f g h k l m : Point) (FK LM KH HM FG GH : Line)
    (hk_FK : k.onLine FK) (hf_FK : f.onLine FK)
    (hm_LM : m.onLine LM) (hl_LM : l.onLine LM) (hml : m ≠ l)
    (hk_KH : k.onLine KH) (hh_KH : h.onLine KH) (hm_HM : m.onLine HM) (step10 : KH = HM)
    (hf_FG : f.onLine FG) (hg_FG : g.onLine FG)
    (hg_GH : g.onLine GH) (hh_GH : h.onLine GH) (hgh : g ≠ h)
    (hfk_ss : f.sameSide k GH)
    (hk_off : ¬k.onLine GH) (hm_off : ¬m.onLine GH) (hmk_ns : ¬m.sameSide k GH)
    (hFGKH : ¬FG.intersectsLine KH)
    (step17 : |(k─f)| = |(m─l)| ∧ ¬(FK.intersectsLine LM))
    (step18 : distinctPointsOnLine k m KH ∧ distinctPointsOnLine f l FG) :
    |(k─m)| = |(f─l)| ∧ ¬(KH.intersectsLine FG) := by
  have hFGKH_ne : FG ≠ KH := by euclid_finish
  have hkf : k ≠ f := by euclid_finish
  have step19_kmss : k.sameSide m FG := by euclid_apply (helper_1_45_step19_kmss g h k m KH HM FG GH (by euclid_assumption "" (show k.onLine KH; assumption)) (by euclid_assumption "" (show h.onLine KH; assumption)) (by euclid_assumption "" (show m.onLine HM; assumption)) (by euclid_assumption "" (show KH = HM; assumption)) (by euclid_assumption "" (show g.onLine FG; assumption)) (by euclid_assumption "" (show g.onLine GH; assumption)) (by euclid_assumption "" (show h.onLine GH; assumption)) (by euclid_assumption "" (show g ≠ h; assumption)) (by euclid_assumption "" (show ¬k.onLine GH; assumption)) (by euclid_assumption "" (show ¬FG.intersectsLine KH; assumption)))
  euclid_apply (proposition_33 k f m l FK LM KH FG)
  euclid_finish

end Elements.Book1

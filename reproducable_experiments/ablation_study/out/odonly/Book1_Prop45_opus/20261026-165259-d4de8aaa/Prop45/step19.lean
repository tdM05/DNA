import SystemE
import Book1.Prop33.Main
import Book1.Prop45.step19_ksm

namespace Elements.Book1

set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

theorem helper_1_45_step19 (f g h k l m : Point) (FG KH HM FK LM GH : Line)
  (hstep17 : |(k─f)| = |(m─l)| ∧ ¬(FK.intersectsLine LM))
  (hstep18 : distinctPointsOnLine k m KH ∧ distinctPointsOnLine f l FG)
  (hkFK : k.onLine FK) (hfFK : f.onLine FK)
  (hmLM : m.onLine LM) (hlLM : l.onLine LM) (hml : m ≠ l)
  (hhKH : h.onLine KH) (hkKH : k.onLine KH) (hmHM : m.onLine HM) (hstep10 : KH = HM)
  (hfFG : f.onLine FG) (hgFG : g.onLine FG)
  (hniFGKH : ¬FG.intersectsLine KH)
  (hgGH : g.onLine GH) (hhGH : h.onLine GH) (hgh : g ≠ h) (hsame : f.sameSide k GH)
  : |(k─m)| = |(f─l)| ∧ ¬(KH.intersectsLine FG) := by
  obtain ⟨hlen, hpar⟩ := hstep17
  obtain ⟨hd1, hd2⟩ := hstep18
  have step19_ksm : k.sameSide m FG := by euclid_apply (helper_1_45_step19_ksm f g h k m FG KH HM GH (by euclid_assumption "" (show k.onLine KH; assumption)) (by euclid_assumption "" (show h.onLine KH; assumption)) (by euclid_assumption "" (show m.onLine HM; assumption)) (by euclid_assumption "" (show KH = HM; assumption)) (by euclid_assumption "" (show ¬FG.intersectsLine KH; assumption)) (by euclid_assumption "" (show f.onLine FG; assumption)) (by euclid_assumption "" (show g.onLine FG; assumption)) (by euclid_assumption "" (show g.onLine GH; assumption)) (by euclid_assumption "" (show h.onLine GH; assumption)) (by euclid_assumption "" (show g ≠ h; assumption)) (by euclid_assumption "" (show f.sameSide k GH; assumption)))
  euclid_apply (proposition_33 k f m l FK LM KH FG)
  euclid_finish

end Elements.Book1

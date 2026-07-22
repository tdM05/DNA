import SystemE
import Book1.Prop33.Main
import Book1.Prop45.step19_kmss

set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step19 (f g h k l m : Point) (FG KH FK GH LM : Line)
    (a1 : f.onLine FG) (a2 : g.onLine FG)
    (a3 : k.onLine KH) (a4 : h.onLine KH)
    (a5 : f.onLine FK) (a6 : k.onLine FK)
    (a7 : g.onLine GH) (a8 : h.onLine GH) (a9 : g ≠ h)
    (a10 : f.sameSide k GH)
    (a11 : ¬FG.intersectsLine KH) (a12 : ¬FK.intersectsLine GH)
    (b7 : m.onLine LM) (b8 : l.onLine LM) (b9 : m ≠ l)
    (hstep17 : |(k─f)| = |(m─l)| ∧ ¬(FK.intersectsLine LM))
    (hstep18 : distinctPointsOnLine k m KH ∧ distinctPointsOnLine f l FG)
    : |(k─m)| = |(f─l)| ∧ ¬(KH.intersectsLine FG) := by
  have step19_kmss : k.sameSide m FG := by euclid_apply (helper_1_45_step19_kmss f g h k l m FG KH FK GH (by euclid_assumption "" (show f.onLine FG; assumption)) (by euclid_assumption "" (show g.onLine FG; assumption)) (by euclid_assumption "" (show k.onLine KH; assumption)) (by euclid_assumption "" (show h.onLine KH; assumption)) (by euclid_assumption "" (show f.onLine FK; assumption)) (by euclid_assumption "" (show k.onLine FK; assumption)) (by euclid_assumption "" (show g.onLine GH; assumption)) (by euclid_assumption "" (show h.onLine GH; assumption)) (by euclid_assumption "" (show g ≠ h; assumption)) (by euclid_assumption "" (show f.sameSide k GH; assumption)) (by euclid_assumption "" (show ¬FG.intersectsLine KH; assumption)) (by euclid_assumption "" (show ¬FK.intersectsLine GH; assumption)) (by euclid_assumption "" (show distinctPointsOnLine k m KH ∧ distinctPointsOnLine f l FG; assumption)))
  euclid_apply (proposition_33 k f m l FK LM KH FG)
  euclid_finish

end Elements.Book1

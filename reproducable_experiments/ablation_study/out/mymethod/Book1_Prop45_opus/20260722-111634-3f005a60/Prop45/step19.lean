import SystemE
import Book1.Prop33.Main
import Helpers.SameSide
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step19 (f g h k l m : Point) (FK LM KH FG GH : Line)
    (hkFK : k.onLine FK) (hfFK : f.onLine FK)
    (hmLM : m.onLine LM) (hlLM : l.onLine LM) (hml : m ≠ l)
    (hstep18 : distinctPointsOnLine k m KH ∧ distinctPointsOnLine f l FG)
    (hstep17 : |(k─f)| = |(m─l)| ∧ ¬(FK.intersectsLine LM))
    (hgFG : g.onLine FG) (hhKH : h.onLine KH)
    (hgGH : g.onLine GH) (hhGH : h.onLine GH) (hgh : g ≠ h)
    (hfFG : f.onLine FG) (hfssk : f.sameSide k GH)
    (hpar1 : ¬FG.intersectsLine KH) :
    |(k─m)| = |(f─l)| ∧ ¬(KH.intersectsLine FG) := by
  have hkKH : k.onLine KH := by euclid_finish
  have hmKH : m.onLine KH := by euclid_finish
  have hKHneFG : KH ≠ FG := by euclid_finish
  have hparFG : ¬(KH.intersectsLine FG) := by euclid_finish
  have hksm : k.sameSide m FG := Elements.sameSide_of_parallel_both k m KH FG hkKH hmKH hKHneFG hparFG
  euclid_apply (proposition_33 k f m l FK LM KH FG)
  euclid_finish

end Elements.Book1

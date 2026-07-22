import SystemE
import Helpers.SameSide
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step20 (f g h k l m : Point) (FG KH FK LM GH : Line)
    (hfFG : f.onLine FG) (hkFK : k.onLine FK) (hfFK : f.onLine FK) (hkKH : k.onLine KH)
    (hstep18 : distinctPointsOnLine k m KH ∧ distinctPointsOnLine f l FG)
    (hstep17 : |(k─f)| = |(m─l)| ∧ ¬(FK.intersectsLine LM))
    (hmLM : m.onLine LM) (hlLM : l.onLine LM) (hml : m ≠ l)
    (hgGH : g.onLine GH) (hhGH : h.onLine GH)
    (hfssk : f.sameSide k GH)
    (hstep9 : k.opposingSides m GH ∧ (∠ k:h:g + ∠ g:h:m = ∟ + ∟))
    (hpar1 : ¬FG.intersectsLine KH) (hparGHLM : ¬GH.intersectsLine LM) :
    formParallelogram f l k m FG KH FK LM := by
  have hlFG : l.onLine FG := by euclid_finish
  have hmKH : m.onLine KH := by euclid_finish
  have hpar17 : ¬(FK.intersectsLine LM) := hstep17.2
  have hfoppm : f.opposingSides m GH := by euclid_finish
  have hFKneLM : FK ≠ LM := by
    intro heq
    have hfLM : f.onLine LM := heq ▸ hfFK
    euclid_finish
  have hfsk_lm : f.sameSide k LM := Elements.sameSide_of_parallel_both f k FK LM hfFK hkFK hFKneLM hpar17
  euclid_finish

end Elements.Book1

import SystemE
import Helpers.SameSide
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step18 (f g h k l m : Point) (KH HM FG GL GH LM : Line)
    (hkKH : k.onLine KH) (hmHM : m.onLine HM) (hstep10 : KH = HM)
    (hfFG : f.onLine FG) (hlGL : l.onLine GL) (hstep16 : FG = GL)
    (hgGH : g.onLine GH) (hhGH : h.onLine GH)
    (hfssk : f.sameSide k GH)
    (hstep9 : k.opposingSides m GH ∧ (∠ k:h:g + ∠ g:h:m = ∟ + ∟))
    (hmLM : m.onLine LM) (hlLM : l.onLine LM) (hssHLM : h.sameSide g LM)
    (hpar2 : ¬GH.intersectsLine LM) :
    distinctPointsOnLine k m KH ∧ distinctPointsOnLine f l FG := by
  have hhoffLM : ¬ h.onLine LM := same_side_not_on_line h g LM hssHLM
  have hne : LM ≠ GH := fun heq => hhoffLM (heq ▸ hhGH)
  have hpar2' : ¬(LM.intersectsLine GH) := by euclid_finish
  have hmssl : m.sameSide l GH := Elements.sameSide_of_parallel_both m l LM GH hmLM hlLM hne hpar2'
  have hfoppl : f.opposingSides l GH := by euclid_finish
  euclid_finish

end Elements.Book1

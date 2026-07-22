import SystemE
import Book1.Prop14.Main
import Helpers.SameSide
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step16 (f g h k l m : Point) (GH FG GL LM : Line)
    (hhGH : h.onLine GH) (hgGH : g.onLine GH) (hgh : g ≠ h)
    (hfFG : f.onLine FG) (hgFG : g.onLine FG)
    (hgGL : g.onLine GL) (hlGL : l.onLine GL)
    (hfssk : f.sameSide k GH)
    (hstep9 : k.opposingSides m GH ∧ (∠ k:h:g + ∠ g:h:m = ∟ + ∟))
    (hmLM : m.onLine LM) (hlLM : l.onLine LM)
    (hssHLM : h.sameSide g LM)
    (hpar2 : ¬GH.intersectsLine LM)
    (hstep15 : ∠ h:g:f + ∠ h:g:l = ∟ + ∟) :
    FG = GL := by
  have hhoffLM : ¬ h.onLine LM := same_side_not_on_line h g LM hssHLM
  have hne : LM ≠ GH := fun heq => hhoffLM (heq ▸ hhGH)
  have hpar2' : ¬(LM.intersectsLine GH) := by euclid_finish
  have hmssl : m.sameSide l GH := Elements.sameSide_of_parallel_both m l LM GH hmLM hlLM hne hpar2'
  have hfl : f.opposingSides l GH := by euclid_finish
  euclid_apply (proposition_14 h g f l GH FG GL)
  euclid_finish

end Elements.Book1

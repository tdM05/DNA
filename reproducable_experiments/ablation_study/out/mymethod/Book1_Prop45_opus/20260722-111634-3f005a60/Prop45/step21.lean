import SystemE
import Helpers.SameSide
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step21 (a b c d f g h k l m : Point) (FG KH FK LM GH : Line)
    (hstep20 : formParallelogram f l k m FG KH FK LM)
    (hstep21a1 : Triangle.area △ f:k:h + Triangle.area △ f:h:g = Triangle.area △ a:b:d)
    (hstep21a2 : Triangle.area △ g:h:m + Triangle.area △ g:l:m = Triangle.area △ d:b:c)
    (hfFG : f.onLine FG) (hgFG : g.onLine FG)
    (hkKH : k.onLine KH) (hhKH : h.onLine KH)
    (hgGH : g.onLine GH) (hhGH : h.onLine GH)
    (hfssk : f.sameSide k GH)
    (hstep9 : k.opposingSides m GH ∧ (∠ k:h:g + ∠ g:h:m = ∟ + ∟))
    (hmLM : m.onLine LM) (hlLM : l.onLine LM) (hssHLM : h.sameSide g LM)
    (hparGHLM : ¬GH.intersectsLine LM) :
    Triangle.area △ f:k:m + Triangle.area △ f:l:m = Triangle.area △ a:b:d + Triangle.area △ d:b:c := by
  have hlFG : l.onLine FG := by euclid_finish
  have hmKH : m.onLine KH := by euclid_finish
  have hhoffLM : ¬ h.onLine LM := same_side_not_on_line h g LM hssHLM
  have hne : LM ≠ GH := fun heq => hhoffLM (heq ▸ hhGH)
  have hpar' : ¬(LM.intersectsLine GH) := by euclid_finish
  have hmssl : m.sameSide l GH := Elements.sameSide_of_parallel_both m l LM GH hmLM hlLM hne hpar'
  have hfoppl : f.opposingSides l GH := by euclid_finish
  have hbfgl : between f g l := by euclid_finish
  have hbkhm : between k h m := by euclid_finish
  euclid_apply (sum_parallelograms_area f l k m g h FG KH FK LM)
  euclid_finish

end Elements.Book1

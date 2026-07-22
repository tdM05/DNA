import SystemE
import Book1.Prop30.Main
import Book1Variants.Prop34
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step17 (f g h k l m : Point) (FG KH FK GH LM : Line)
    (hstep17a1 : |(f─k)| = |(h─g)| ∧ ¬(FK.intersectsLine GH))
    (hstep17a2 : |(h─g)| = |(m─l)| ∧ ¬(GH.intersectsLine LM))
    (hfFG : f.onLine FG) (hgFG : g.onLine FG)
    (hkKH : k.onLine KH) (hhKH : h.onLine KH)
    (hfFK : f.onLine FK) (hkFK : k.onLine FK)
    (hlLM : l.onLine LM) (hmLM : m.onLine LM)
    (hgGH : g.onLine GH) (hhGH : h.onLine GH)
    (hgh : g ≠ h)
    (hfssk : f.sameSide k GH)
    (hparFGKH : ¬FG.intersectsLine KH) (hparFKGH : ¬(FK.intersectsLine GH))
    (hstep9 : k.opposingSides m GH ∧ (∠ k:h:g + ∠ g:h:m = ∟ + ∟))
    (hssHLM : h.sameSide g LM) :
    |(k─f)| = |(m─l)| ∧ ¬(FK.intersectsLine LM) := by
  -- $FK$ is equal and parallel to $HG$ [Prop.~1.34]: realise the citation from parallelogram $FGKH$.
  euclid_apply (proposition_34' f g k h FG KH FK GH)
  have hfoffGH : ¬ f.onLine GH := same_side_not_on_line f k GH hfssk
  have hFKneGH : FK ≠ GH := fun heq => hfoffGH (heq ▸ hfFK)
  have hhoffLM : ¬ h.onLine LM := same_side_not_on_line h g LM hssHLM
  have hLMneGH : LM ≠ GH := fun heq => hhoffLM (heq ▸ hhGH)
  have hfoppm : f.opposingSides m GH := by euclid_finish
  have hFKneLM : FK ≠ LM := by
    intro heq
    have hfLM : f.onLine LM := heq ▸ hfFK
    euclid_finish
  -- $KF$ is thus also equal and parallel to $ML$ [Prop.~1.30].
  euclid_apply (proposition_30 FK LM GH)
  euclid_finish

end Elements.Book1

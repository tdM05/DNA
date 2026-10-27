import SystemE
import Book1Variants.Prop34
import Book1.Prop30.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step17 (f g h k l m : Point) (FG KH FK GH LM : Line)
    (hassump1 : |(f─k)| = |(h─g)| ∧ ¬(FK.intersectsLine GH))
    (hassump2 : |(h─g)| = |(m─l)| ∧ ¬(GH.intersectsLine LM))
    (hf_FG : f.onLine FG) (hg_FG : g.onLine FG)
    (hk_KH : k.onLine KH) (hh_KH : h.onLine KH)
    (hf_FK : f.onLine FK) (hk_FK : k.onLine FK)
    (hg_GH : g.onLine GH) (hh_GH : h.onLine GH) (hgh_ne : g ≠ h)
    (hss : f.sameSide k GH)
    (hni1 : ¬(FG.intersectsLine KH)) (hni2 : ¬(FK.intersectsLine GH))
    (hm_LM : m.onLine LM) (hl_LM : l.onLine LM)
    (hm_notGH : ¬(m.onLine GH)) (hk_notGH : ¬(k.onLine GH)) (hmk_ss : ¬(m.sameSide k GH)) :
    |(k─f)| = |(m─l)| ∧ ¬(FK.intersectsLine LM) := by
  euclid_apply (proposition_34' f g k h FG KH FK GH)
  have hklm : ¬k.onLine LM := by euclid_finish
  euclid_apply (proposition_30 FK LM GH)
  euclid_finish

end Elements.Book1

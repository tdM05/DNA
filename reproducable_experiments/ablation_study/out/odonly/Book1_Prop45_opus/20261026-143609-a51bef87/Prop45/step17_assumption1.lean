import SystemE
import Book1Variants.Prop34
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step17_assumption1 (f g h k : Point) (FG KH FK GH : Line)
    (hf_FG : f.onLine FG) (hg_FG : g.onLine FG)
    (hk_KH : k.onLine KH) (hh_KH : h.onLine KH)
    (hf_FK : f.onLine FK) (hk_FK : k.onLine FK)
    (hg_GH : g.onLine GH) (hh_GH : h.onLine GH) (hgh_ne : g ≠ h)
    (hss : f.sameSide k GH)
    (hni1 : ¬(FG.intersectsLine KH)) (hni2 : ¬(FK.intersectsLine GH)) :
    |(f─k)| = |(h─g)| ∧ ¬(FK.intersectsLine GH) := by
  euclid_apply (proposition_34' f g k h FG KH FK GH)
  euclid_finish

end Elements.Book1

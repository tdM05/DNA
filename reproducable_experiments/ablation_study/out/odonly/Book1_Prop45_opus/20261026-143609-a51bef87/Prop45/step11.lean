import SystemE
import Book1Variants.Prop29
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step11 (f g h k m : Point) (FG KH HM GH : Line)
    (hassump1 : ¬(FG.intersectsLine KH))
    (hf_FG : f.onLine FG) (hg_FG : g.onLine FG)
    (hh_HM : h.onLine HM) (hm_HM : m.onLine HM)
    (hg_GH : g.onLine GH) (hh_GH : h.onLine GH) (hgh_ne : g ≠ h)
    (hss : f.sameSide k GH)
    (hm_notGH : ¬(m.onLine GH)) (hk_notGH : ¬(k.onLine GH)) (hmk_ss : ¬(m.sameSide k GH))
    (hstep10 : KH = HM) :
    ∠ m:h:g = ∠ h:g:f := by
  euclid_apply (proposition_29''' f m g h FG HM GH)
  euclid_finish

end Elements.Book1

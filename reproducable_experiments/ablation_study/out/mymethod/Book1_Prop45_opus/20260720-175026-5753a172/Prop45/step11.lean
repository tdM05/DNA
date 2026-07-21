import SystemE
import Book1Variants.Prop29
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step11
  (f g h k m : Point) (FG GH HM KH : Line)
  (hf_FG : f.onLine FG) (hg_FG : g.onLine FG)
  (hg_GH : g.onLine GH) (hh_GH : h.onLine GH) (hgh : g ≠ h)
  (hh_HM : h.onLine HM) (hm_HM : m.onLine HM)
  (hfk_ss : f.sameSide k GH) (hmk_ss : ¬m.sameSide k GH)
  (hm_off : ¬m.onLine GH) (hk_off : ¬k.onLine GH)
  (step10 : KH = HM)
  (hassump1 : ¬(FG.intersectsLine KH))
  : ∠ m:h:g = ∠ h:g:f := by
  euclid_apply (proposition_29''' f m g h FG HM GH)
  euclid_finish

end Elements.Book1

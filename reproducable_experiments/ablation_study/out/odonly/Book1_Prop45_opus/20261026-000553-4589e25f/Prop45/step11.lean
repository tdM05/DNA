import SystemE
import Book1Variants.Prop29
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step11 (f g h k m : Point) (FG KH GH HM : Line)
    (hf_FG : f.onLine FG) (hg_FG : g.onLine FG)
    (hh_KH : h.onLine KH) (hm_HM : m.onLine HM) (step10 : KH = HM)
    (hg_GH : g.onLine GH) (hh_GH : h.onLine GH) (hgh : g ≠ h)
    (hfk_ss : f.sameSide k GH)
    (hm_off : ¬m.onLine GH) (hk_off : ¬k.onLine GH) (hmk_ns : ¬m.sameSide k GH)
    -- Reasoning hypotheses (from @assumption — keep these types in the signature):
    (hassump1 : ¬(FG.intersectsLine KH))   -- "the straight-line $HG$ falls across the parallels $KM$ and $FG$"
    : ∠ m:h:g = ∠ h:g:f := by
  have hmKH : m.onLine KH := by rw [step10]; exact hm_HM
  have hfm_opp : f.opposingSides m GH := by euclid_finish
  euclid_apply (proposition_29''' f m g h FG KH GH)
  euclid_finish

end Elements.Book1

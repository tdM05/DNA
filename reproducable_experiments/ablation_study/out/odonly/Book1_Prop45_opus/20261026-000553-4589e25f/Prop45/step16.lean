import SystemE
import Book1.Prop14.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step16 (f g h k l m : Point) (GH FG GL LM : Line)
    (hg_GH : g.onLine GH) (hh_GH : h.onLine GH) (hgh : g ≠ h)
    (hf_FG : f.onLine FG) (hg_FG : g.onLine FG)
    (hg_GL : g.onLine GL) (hl_GL : l.onLine GL)
    (hfk_ss : f.sameSide k GH)
    (hk_off : ¬k.onLine GH) (hm_off : ¬m.onLine GH) (hmk_ns : ¬m.sameSide k GH)
    (hm_LM : m.onLine LM) (hl_LM : l.onLine LM) (hGHLM : ¬GH.intersectsLine LM)
    (step15 : ∠ h:g:f + ∠ h:g:l = ∟ + ∟) :
    FG = GL := by
  have hfl_opp : f.opposingSides l GH := by euclid_finish
  euclid_apply (proposition_14 h g f l GH FG GL)
  euclid_finish

end Elements.Book1

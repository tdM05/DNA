import SystemE
import Book1.Prop14.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step16 (f g h k l m : Point) (FG GL GH LM : Line)
    (hstep15 : ∠ h:g:f + ∠ h:g:l = ∟ + ∟)
    (hf_FG : f.onLine FG) (hg_FG : g.onLine FG)
    (hg_GL : g.onLine GL) (hl_GL : l.onLine GL)
    (hg_GH : g.onLine GH) (hh_GH : h.onLine GH) (hgh_ne : g ≠ h)
    (hss_fk : f.sameSide k GH)
    (hk_notGH : ¬(k.onLine GH)) (hm_notGH : ¬(m.onLine GH)) (hmk_ss : ¬(m.sameSide k GH))
    (hl_LM : l.onLine LM) (hm_LM : m.onLine LM) (hni_GHLM : ¬(GH.intersectsLine LM)) :
    FG = GL := by
  euclid_apply (proposition_14 h g f l GH FG GL)
  euclid_finish

end Elements.Book1

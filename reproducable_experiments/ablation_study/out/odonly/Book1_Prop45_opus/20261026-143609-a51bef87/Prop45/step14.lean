import SystemE
import Book1Variants.Prop29
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step14 (g h l m : Point) (HM GL GH LM : Line)
    (hg_GL : g.onLine GL) (hl_GL : l.onLine GL)
    (hh_HM : h.onLine HM) (hm_HM : m.onLine HM)
    (hg_GH : g.onLine GH) (hh_GH : h.onLine GH) (hgh_ne : g ≠ h)
    (hm_LM : m.onLine LM) (hl_LM : l.onLine LM) (hml_ne : m ≠ l)
    (hssLM : h.sameSide g LM)
    (hni_HMGL : ¬(HM.intersectsLine GL)) (hni_GHLM : ¬(GH.intersectsLine LM))
    (hm_notGH : ¬(m.onLine GH)) :
    ∠ m:h:g + ∠ h:g:l = ∟ + ∟ := by
  euclid_apply (proposition_29''''' l m g h GL HM GH)
  euclid_finish

end Elements.Book1

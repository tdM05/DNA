import SystemE
import Book1Variants.Prop29
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step14 (g h l m : Point) (KH HM GL GH LM : Line)
    (step10 : KH = HM)
    (hh_HM : h.onLine HM) (hm_HM : m.onLine HM)
    (hg_GL : g.onLine GL) (hl_GL : l.onLine GL)
    (hg_GH : g.onLine GH) (hh_GH : h.onLine GH) (hgh : g ≠ h)
    (hm_LM : m.onLine LM) (hl_LM : l.onLine LM)
    (hm_off : ¬m.onLine GH)
    (hHMGL : ¬HM.intersectsLine GL) (hGHLM : ¬GH.intersectsLine LM) :
    ∠ m:h:g + ∠ h:g:l = ∟ + ∟ := by
  have hhKH : h.onLine KH := by rw [step10]; exact hh_HM
  have hmKH : m.onLine KH := by rw [step10]; exact hm_HM
  have hKHGL : ¬KH.intersectsLine GL := by rw [step10]; exact hHMGL
  have hml_ss : m.sameSide l GH := by euclid_finish
  euclid_apply (proposition_29''''' m l h g KH GL GH)
  euclid_finish

end Elements.Book1

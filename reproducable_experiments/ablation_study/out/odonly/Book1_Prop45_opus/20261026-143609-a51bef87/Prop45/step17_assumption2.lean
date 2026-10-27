import SystemE
import Book1Variants.Prop34
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step17_assumption2 (g h l m : Point) (HM GL GH LM : Line)
    (hh_HM : h.onLine HM) (hm_HM : m.onLine HM)
    (hg_GL : g.onLine GL) (hl_GL : l.onLine GL)
    (hh_GH : h.onLine GH) (hg_GH : g.onLine GH)
    (hm_LM : m.onLine LM) (hl_LM : l.onLine LM) (hml_ne : m ≠ l)
    (hss : h.sameSide g LM)
    (hni1 : ¬(HM.intersectsLine GL)) (hni2 : ¬(GH.intersectsLine LM)) :
    |(h─g)| = |(m─l)| ∧ ¬(GH.intersectsLine LM) := by
  euclid_apply (proposition_34' h m g l HM GL GH LM)
  euclid_finish

end Elements.Book1

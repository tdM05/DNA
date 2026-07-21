import SystemE
import Book1.Prop34.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step17_assumption2
  (h m g l : Point) (HM GL GH LM : Line)
  (hh_HM : h.onLine HM) (hm_HM : m.onLine HM)
  (hg_GL : g.onLine GL) (hl_GL : l.onLine GL)
  (hh_GH : h.onLine GH) (hg_GH : g.onLine GH)
  (hm_LM : m.onLine LM) (hl_LM : l.onLine LM) (hml : m ≠ l)
  (hhg_LM : h.sameSide g LM)
  (hHMGL : ¬HM.intersectsLine GL) (hGHLM : ¬GH.intersectsLine LM) :
  |(h─g)| = |(m─l)| ∧ ¬(GH.intersectsLine LM) := by
  euclid_apply (line_from_points m g) as MG
  euclid_apply (proposition_34 h m g l HM GL GH LM MG)
  euclid_finish

end Elements.Book1

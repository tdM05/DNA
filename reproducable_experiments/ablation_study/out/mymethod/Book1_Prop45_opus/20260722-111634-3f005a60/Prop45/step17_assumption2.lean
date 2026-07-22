import SystemE
import Book1Variants.Prop34
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step17_assumption2 (g h l m : Point) (HM GL GH LM : Line)
    (hhHM : h.onLine HM) (hmHM : m.onLine HM) (hgGL : g.onLine GL) (hlGL : l.onLine GL)
    (hhGH : h.onLine GH) (hgGH : g.onLine GH) (hmLM : m.onLine LM) (hlLM : l.onLine LM)
    (hml : m ≠ l) (hss : h.sameSide g LM)
    (hpar1 : ¬HM.intersectsLine GL) (hpar2 : ¬GH.intersectsLine LM) :
    |(h─g)| = |(m─l)| ∧ ¬(GH.intersectsLine LM) := by
  euclid_apply (proposition_34' h m g l HM GL GH LM)
  euclid_finish

end Elements.Book1

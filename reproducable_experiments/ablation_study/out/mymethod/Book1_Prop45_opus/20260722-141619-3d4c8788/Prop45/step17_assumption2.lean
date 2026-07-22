import SystemE
import Book1Variants.Prop34

set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step17_assumption2 (g h l m : Point) (HM GL GH LM : Line)
    (h1 : h.onLine HM) (h2 : m.onLine HM)
    (h3 : g.onLine GL) (h4 : l.onLine GL)
    (h5 : h.onLine GH) (h6 : g.onLine GH)
    (h7 : m.onLine LM) (h8 : l.onLine LM) (h9 : m ≠ l)
    (h10 : h.sameSide g LM)
    (h11 : ¬HM.intersectsLine GL) (h12 : ¬GH.intersectsLine LM)
    : |(h─g)| = |(m─l)| ∧ ¬(GH.intersectsLine LM) := by
  euclid_apply (proposition_34' h m g l HM GL GH LM)
  euclid_finish

end Elements.Book1

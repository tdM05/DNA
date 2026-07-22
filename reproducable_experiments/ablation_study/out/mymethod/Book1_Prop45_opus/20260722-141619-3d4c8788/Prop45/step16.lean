import SystemE
import Book1.Prop14.Main

set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step16 (f g h k l m : Point) (FG HM GL GH LM : Line)
    (p1 : h.onLine HM) (p2 : m.onLine HM)
    (p3 : g.onLine GL) (p4 : l.onLine GL)
    (p5 : h.onLine GH) (p6 : g.onLine GH)
    (p7 : m.onLine LM) (p8 : l.onLine LM) (p9 : m ≠ l)
    (p10 : h.sameSide g LM)
    (p11 : ¬HM.intersectsLine GL) (p12 : ¬GH.intersectsLine LM)
    (q1 : f.onLine FG) (q2 : g.onLine FG)
    (q3 : f.sameSide k GH) (q4 : ¬m.sameSide k GH)
    (hstep15 : ∠ h:g:f + ∠ h:g:l = ∟ + ∟)
    : FG = GL := by
  euclid_apply (parallelogram_same_side h m g l HM GL GH LM)
  euclid_apply (proposition_14 h g f l GH FG GL)
  euclid_finish

end Elements.Book1

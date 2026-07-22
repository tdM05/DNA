import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step18 (f g h k l m : Point) (FG KH GH HM GL LM : Line)
    (a1 : f.onLine FG) (a2 : g.onLine FG)
    (a3 : k.onLine KH) (a4 : h.onLine KH)
    (a7 : g.onLine GH) (a8 : h.onLine GH)
    (a10 : f.sameSide k GH)
    (b1 : h.onLine HM) (b2 : m.onLine HM)
    (b3 : g.onLine GL) (b4 : l.onLine GL)
    (b7 : m.onLine LM) (b8 : l.onLine LM) (b9 : m ≠ l)
    (b10 : h.sameSide g LM)
    (b11 : ¬HM.intersectsLine GL) (b12 : ¬GH.intersectsLine LM)
    (c1 : ¬k.onLine GH) (c2 : ¬m.onLine GH) (c3 : ¬m.sameSide k GH)
    (hstep10 : KH = HM) (hstep16 : FG = GL)
    : distinctPointsOnLine k m KH ∧ distinctPointsOnLine f l FG := by
  euclid_apply (parallelogram_same_side h m g l HM GL GH LM)
  euclid_finish

end Elements.Book1

import SystemE

set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step21_bfgl (f g h k l m : Point) (FG GH HM GL LM : Line)
    (a1 : f.onLine FG) (a2 : g.onLine FG) (a7 : g.onLine GH) (a8 : h.onLine GH)
    (hlFG : l.onLine FG) (hfl : f ≠ l)
    (a10 : f.sameSide k GH)
    (hstep9 : k.opposingSides m GH ∧ (∠ k:h:g + ∠ g:h:m = ∟ + ∟))
    (b1 : h.onLine HM) (b2 : m.onLine HM) (b3 : g.onLine GL) (b4 : l.onLine GL)
    (b7 : m.onLine LM) (b8 : l.onLine LM) (b9 : m ≠ l)
    (b10 : h.sameSide g LM) (b11 : ¬HM.intersectsLine GL) (b12 : ¬GH.intersectsLine LM)
    : between f g l := by
  have hpar2 := parallelogram_same_side h m g l HM GL GH LM
    ⟨b1, b2, b3, b4, a8, a7, ⟨b7, b8, b9⟩, b10, b11, b12⟩
  have hml : m.sameSide l GH := hpar2.1
  euclid_finish

end Elements.Book1

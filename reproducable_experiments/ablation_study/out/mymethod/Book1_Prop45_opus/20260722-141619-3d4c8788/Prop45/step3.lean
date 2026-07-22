import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step3 (b c d e₁ e₂ e₃ g h m l : Point) (HM GL GH LM : Line)
    (h1 : h.onLine HM) (h2 : m.onLine HM)
    (h3 : g.onLine GL) (h4 : l.onLine GL)
    (h5 : h.onLine GH) (h6 : g.onLine GH)
    (h7 : m.onLine LM) (h8 : l.onLine LM) (h9 : m ≠ l)
    (h10 : h.sameSide g LM)
    (h11 : ¬HM.intersectsLine GL) (h12 : ¬GH.intersectsLine LM)
    (hang : ∠ g:h:m = ∠ e₁:e₂:e₃)
    (harea : Triangle.area △ g:h:m + Triangle.area △ g:l:m = Triangle.area △ d:b:c) :
    formParallelogram h m g l HM GL GH LM ∧ (∠ g:h:m = ∠ e₁:e₂:e₃) ∧
      (Triangle.area △ g:h:m + Triangle.area △ g:l:m = Triangle.area △ d:b:c) := by
  euclid_finish

end Elements.Book1

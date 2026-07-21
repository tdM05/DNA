import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step3
    (b c d e₁ e₂ e₃ g h m l : Point) (HM GL GH LM : Line)
    (hh_HM : h.onLine HM) (hm_HM : m.onLine HM)
    (hg_GL : g.onLine GL) (hl_GL : l.onLine GL)
    (hh_GH : h.onLine GH) (hg_GH : g.onLine GH)
    (hm_LM : m.onLine LM) (hl_LM : l.onLine LM) (hml : m ≠ l)
    (hhg_LM : h.sameSide g LM)
    (hHMGL : ¬HM.intersectsLine GL) (hGHLM : ¬GH.intersectsLine LM)
    (hangle : ∠ g:h:m = ∠ e₁:e₂:e₃)
    (harea : Triangle.area △ g:h:m + Triangle.area △ g:l:m = Triangle.area △ d:b:c) :
    formParallelogram h m g l HM GL GH LM ∧ (∠ g:h:m = ∠ e₁:e₂:e₃) ∧
      (Triangle.area △ g:h:m + Triangle.area △ g:l:m = Triangle.area △ d:b:c) := by
  euclid_finish

end Elements.Book1

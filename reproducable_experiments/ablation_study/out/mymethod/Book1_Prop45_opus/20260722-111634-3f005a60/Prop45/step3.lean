import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step3 (b c d e₁ e₂ e₃ g h m l : Point) (HM GL GH LM : Line)
    (hhHM : h.onLine HM) (hmHM : m.onLine HM)
    (hgGL : g.onLine GL) (hlGL : l.onLine GL)
    (hgGH : g.onLine GH) (hhGH : h.onLine GH)
    (hmLM : m.onLine LM) (hlLM : l.onLine LM)
    (hss : h.sameSide g LM) (hml : m ≠ l)
    (hpar1 : ¬HM.intersectsLine GL) (hpar2 : ¬GH.intersectsLine LM)
    (hang : ∠ g:h:m = ∠ e₁:e₂:e₃)
    (harea : Triangle.area △ g:h:m + Triangle.area △ g:l:m = Triangle.area △ d:b:c) :
    formParallelogram h m g l HM GL GH LM ∧ (∠ g:h:m = ∠ e₁:e₂:e₃) ∧
      (Triangle.area △ g:h:m + Triangle.area △ g:l:m = Triangle.area △ d:b:c) := by
  euclid_finish

end Elements.Book1

import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step3 (b c d e₁ e₂ e₃ g h m l : Point) (HM GL GH LM : Line)
  (hhHM : h.onLine HM) (hmHM : m.onLine HM)
  (hgGL : g.onLine GL) (hlGL : l.onLine GL)
  (hhGH : h.onLine GH) (hgGH : g.onLine GH)
  (hmLM : m.onLine LM) (hlLM : l.onLine LM) (hml : m ≠ l)
  (hsame : h.sameSide g LM)
  (hni1 : ¬HM.intersectsLine GL) (hni2 : ¬GH.intersectsLine LM)
  (hangle : ∠ g:h:m = ∠ e₁:e₂:e₃)
  (harea : Triangle.area △ g:h:m + Triangle.area △ g:l:m = Triangle.area △ d:b:c)
  : formParallelogram h m g l HM GL GH LM ∧ (∠ g:h:m = ∠ e₁:e₂:e₃) ∧
      (Triangle.area △ g:h:m + Triangle.area △ g:l:m = Triangle.area △ d:b:c) := by euclid_finish

end Elements.Book1

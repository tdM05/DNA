import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step21_bfgl (f g l : Point) (FG GL GH : Line)
  (hfolg : f.opposingSides l GH) (hgGH : g.onLine GH)
  (hfFG : f.onLine FG) (hgFG : g.onLine FG)
  (hlGL : l.onLine GL) (hstep16 : FG = GL)
  : between f g l := by euclid_finish

end Elements.Book1

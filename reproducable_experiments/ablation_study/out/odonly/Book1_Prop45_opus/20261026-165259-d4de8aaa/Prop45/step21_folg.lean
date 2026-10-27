import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step21_folg (f g h k l m : Point) (GH LM : Line)
  (hsame : f.sameSide k GH) (hopp : k.opposingSides m GH)
  (hlLM : l.onLine LM) (hmLM : m.onLine LM) (hniLMGH : ¬GH.intersectsLine LM)
  (hgGH : g.onLine GH) (hsameLM : h.sameSide g LM)
  : f.opposingSides l GH := by
  have hlsm : l.sameSide m GH := by euclid_finish
  euclid_finish

end Elements.Book1

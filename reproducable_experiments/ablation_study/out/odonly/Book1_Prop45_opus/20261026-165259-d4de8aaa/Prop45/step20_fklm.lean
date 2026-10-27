import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step20_fklm (f k m : Point) (FK LM GH : Line)
  (hfFK : f.onLine FK) (hkFK : k.onLine FK)
  (hpar : ¬FK.intersectsLine LM) (hmLM : m.onLine LM)
  (hopp : k.opposingSides m GH) (hniLMGH : ¬GH.intersectsLine LM)
  : f.sameSide k LM := by
  have hfklm : FK ≠ LM := by euclid_finish
  have hfLM : ¬f.onLine LM := by euclid_finish
  have hkLM : ¬k.onLine LM := by euclid_finish
  euclid_finish

end Elements.Book1

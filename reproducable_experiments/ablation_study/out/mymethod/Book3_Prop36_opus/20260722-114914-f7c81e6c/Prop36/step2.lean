import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step2
  (f b : Point) (ABC : Circle) (FB : Line)
  (hb : b.onCircle ABC) (hfFB : f.onLine FB) (hbFB : b.onLine FB)
  -- Reasoning hypotheses (from @assumption — keep these types in the signature):
  (hassump1 : f.isCentre ABC)   -- "$F$ be the center of circle $ABC$"
  : distinctPointsOnLine f b FB := by euclid_finish

end Elements.Book3

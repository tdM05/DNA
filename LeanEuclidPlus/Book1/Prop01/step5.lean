import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_1_step5 (a b c : Point) (ACE : Circle)
  -- Reasoning hypotheses (from @assumption — keep these types in the signature):
  (hassump1 : b.isCentre ACE)   -- "the point $B$ is the center of the circle $CAE$"
  (ha_ace : a.onCircle ACE) (hc_ace : c.onCircle ACE)
  : |(b─c)| = |(b─a)| := by euclid_finish

end Elements.Book1

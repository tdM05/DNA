import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_1_step4 (a b c : Point) (BCD : Circle)
  -- Reasoning hypotheses (from @assumption — keep these types in the signature):
  (hassump1 : a.isCentre BCD)   -- "the point $A$ is the center of the circle $CDB$"
  (hb_bcd : b.onCircle BCD) (hc_bcd : c.onCircle BCD)
  : |(a─c)| = |(a─b)| := by euclid_finish

end Elements.Book1

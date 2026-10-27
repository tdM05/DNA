import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- TODO: fill object/hypothesis binders (run --context step19)
theorem helper_3_36_step19
  (a c f : Point)
  (hassump1 : |(a─f)| = |(f─c)|)   -- "the straight-line $AC$ is cut in half at point $F$"
  : |(a─f)| = |(f─c)| := by
  exact hassump1

end Elements.Book3

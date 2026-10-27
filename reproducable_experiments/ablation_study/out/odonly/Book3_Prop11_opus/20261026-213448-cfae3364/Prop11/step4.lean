import SystemE
import Mathlib.Tactic.Linarith
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_11_step4 (a f g h : Point)
    (h_bet_fgh : between f g h)
    (step3 : |(a─g)| > |(f─h)| - |(g─f)|) :
    |(a─g)| > |(g─h)| := by
  have heq : |(f─g)| + |(g─h)| = |(f─h)| := between_if f g h h_bet_fgh
  have hsymm : |(g─f)| = |(f─g)| := segment_symmetric g f
  linarith

end Elements.Book3

import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_13_s11
    (s3 : ∠ c:b:e = ∟ ∧ ∠ e:b:d = ∟) :
    ∠ c:b:e + ∠ e:b:d = ∟ + ∟ := by
  linarith [s3.1, s3.2]

end Elements.Book1

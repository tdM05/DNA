import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_46_s17
    (a b d e : Point)
    (s13 : ∠ b:a:d = ∟)
    (s14 : ∠ a:d:e = ∟)
    (s16 : ∠ a:b:e = ∟ ∧ ∠ b:e:d = ∟) :
    ∠ b:a:d = ∟ ∧ ∠ a:d:e = ∟ ∧ ∠ a:b:e = ∟ ∧ ∠ b:e:d = ∟ :=
  ⟨s13, s14, s16.1, s16.2⟩

end Elements.Book1

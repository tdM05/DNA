import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_5_s10 (a b c f g : Point)
    (h_s8 : ∠a:c:f = ∠a:b:g ∧ ∠a:f:c = ∠a:g:b) :
    ∠ a:f:c = ∠ a:g:b :=
  h_s8.2

end Elements.Book1

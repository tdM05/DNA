import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_5_s18 (b c f g : Point)
    (h_s17 : (∠ f:b:c = ∠ g:c:b) ∧ (∠ f:c:b = ∠ g:b:c)) :
    ∠ f:b:c = ∠ g:c:b := h_s17.1

end Elements.Book1

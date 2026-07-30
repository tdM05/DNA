import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_29_s11
    (s10 : ¬(∠ a:g:h ≠ ∠ g:h:d)) :
    ∠ a:g:h = ∠ g:h:d := Classical.not_not.mp s10

end Elements.Book1

import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_29_s15
    (s13 : ∠ e:g:b = ∠ g:h:d)
    (s14 : ∠ e:g:b = ∠ g:h:d → ∠ e:g:b + ∠ b:g:h = ∠ b:g:h + ∠ g:h:d) :
    ∠ e:g:b + ∠ b:g:h = ∠ b:g:h + ∠ g:h:d := s14 s13

end Elements.Book1

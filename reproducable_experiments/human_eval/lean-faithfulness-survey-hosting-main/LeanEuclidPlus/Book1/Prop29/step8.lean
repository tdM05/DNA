import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_29_s8
    (AB CD : Line)
    (s6 : ∠ b:g:h + ∠ g:h:d < ∟ + ∟)
    (s7 : ∠ b:g:h + ∠ g:h:d < ∟ + ∟ → AB.intersectsLine CD) :
    AB.intersectsLine CD := s7 s6

end Elements.Book1

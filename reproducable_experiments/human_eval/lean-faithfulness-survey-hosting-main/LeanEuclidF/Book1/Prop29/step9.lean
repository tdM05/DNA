import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_29_s9
    (AB CD : Line)
    (s8 : AB.intersectsLine CD)
    (s9_a1 : ¬(AB.intersectsLine CD)) :
    False := s9_a1 s8

end Elements.Book1

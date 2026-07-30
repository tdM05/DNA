import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_46_s8
    (a b d : Point)
    (s2 : |(a─d)| = |(a─b)|) :
    |(a─b)| = |(a─d)| := s2.symm

end Elements.Book1

import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_9_s2 (a c d e : Point)
    (hbetween : between a e c) (heq : |(a─e)| = |(a─d)|) :
    between a e c ∧ |(a─e)| = |(a─d)| := ⟨hbetween, heq⟩

end Elements.Book1

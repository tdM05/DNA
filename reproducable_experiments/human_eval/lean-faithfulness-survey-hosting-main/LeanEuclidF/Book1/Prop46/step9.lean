import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_46_s9
    (a b d e : Point)
    (s2 : |(a─d)| = |(a─b)|)
    (s6 : |(a─b)| = |(d─e)|)
    (s7 : |(a─d)| = |(b─e)|) :
    |(b─a)| = |(a─d)| ∧ |(a─d)| = |(d─e)| ∧ |(d─e)| = |(e─b)| := by
  refine ⟨?_, ?_, ?_⟩ <;> euclid_finish

end Elements.Book1

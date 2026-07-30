import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_46_s19
    (a b d e : Point)
    (s17 : ∠ b:a:d = ∟ ∧ ∠ a:d:e = ∟ ∧ ∠ a:b:e = ∟ ∧ ∠ b:e:d = ∟)
    (s18 : |(b─a)| = |(a─d)| ∧ |(a─d)| = |(d─e)| ∧ |(d─e)| = |(e─b)|) :
    (|(b─a)| = |(a─d)| ∧ |(a─d)| = |(d─e)| ∧ |(d─e)| = |(e─b)|) ∧
      (∠ b:a:d = ∟ ∧ ∠ a:d:e = ∟ ∧ ∠ a:b:e = ∟ ∧ ∠ b:e:d = ∟) :=
  ⟨s18, s17⟩

end Elements.Book1

import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_12_s3 (e h g : Point) (hbetween : between e h g) (hlen : |(e─h)| = |(h─g)|) :
    between e h g ∧ |(e─h)| = |(h─g)| :=
  ⟨hbetween, hlen⟩

end Elements.Book1

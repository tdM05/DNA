import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_5_s13 (b c f g : Point)
    (h_s11 : |(b─f)| = |(c─g)|)
    (h_s12 : |(f─c)| = |(g─b)|) :
    (|(b─f)| = |(c─g)|) ∧ (|(f─c)| = |(g─b)|) :=
  ⟨h_s11, h_s12⟩

end Elements.Book1

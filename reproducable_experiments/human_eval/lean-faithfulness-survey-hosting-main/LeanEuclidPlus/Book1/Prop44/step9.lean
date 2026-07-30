import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1
open Elements

theorem h_1_44_s9
    (b e f g h : Point) (HB EF : Line)
    (s7 : ∠ b:h:f + ∠ f:g:e < ∟ + ∟)
    (s8 : ∠ b:h:f + ∠ f:g:e < ∟ + ∟ → HB.intersectsLine EF)
    : HB.intersectsLine EF :=
  s8 s7

end Elements.Book1

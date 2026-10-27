import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step8 (f g h k m : Point)
    (step6 : ∠ f:k:h + ∠ k:h:g = ∠ k:h:g + ∠ g:h:m)
    (step7 : ∠ f:k:h + ∠ k:h:g = ∟ + ∟) :
    ∠ k:h:g + ∠ g:h:m = ∟ + ∟ := by
  euclid_finish

end Elements.Book1

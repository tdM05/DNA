import SystemE
import Book1Variants.Prop29
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step14
  (b c d e₁ e₂ e₃ g h l m : Point) (HM GL GH LM : Line)
  (hgh : g ≠ h)
  (step3 : formParallelogram h m g l HM GL GH LM ∧ (∠ g:h:m = ∠ e₁:e₂:e₃) ∧
      (Triangle.area △ g:h:m + Triangle.area △ g:l:m = Triangle.area △ d:b:c)) :
  ∠ m:h:g + ∠ h:g:l = ∟ + ∟ := by
  euclid_apply (proposition_29''''' l m g h GL HM GH)
  euclid_finish

end Elements.Book1

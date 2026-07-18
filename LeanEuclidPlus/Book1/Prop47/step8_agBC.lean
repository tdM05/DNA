import SystemE
import Helpers.Pasch
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_47_step8_agBC
    (a c g : Point) (BC : Line)
    (hcBC : c.onLine BC) (haoffBC : ¬a.onLine BC) (hcag : between c a g) :
    a.sameSide g BC := by
  euclid_apply (Elements.sameSide_of_between c a g BC)
  euclid_finish

end Elements.Book1

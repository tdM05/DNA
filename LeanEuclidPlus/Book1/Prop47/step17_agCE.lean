import SystemE
import Helpers.Pasch
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_47_step17_agCE
    (a c g : Point) (CE : Line)
    (hcCE : c.onLine CE) (haoffCE : ¬a.onLine CE) (hcag : between c a g) :
    a.sameSide g CE := by
  euclid_apply (Elements.sameSide_of_between c a g CE)
  euclid_finish

end Elements.Book1

import SystemE
import Helpers.Pasch
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_47_step8_ahBC
    (a b h : Point) (BC : Line)
    (hbBC : b.onLine BC) (haoffBC : ¬a.onLine BC) (hbah : between b a h) :
    a.sameSide h BC := by
  euclid_apply (Elements.sameSide_of_between b a h BC)
  euclid_finish

end Elements.Book1

import SystemE
import Helpers.Pasch
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_47_step8_ahBD
    (a b h : Point) (BD : Line)
    (hbBD : b.onLine BD) (haoffBD : ¬a.onLine BD) (hbah : between b a h) :
    a.sameSide h BD := by
  euclid_apply (Elements.sameSide_of_between b a h BD)
  euclid_finish

end Elements.Book1

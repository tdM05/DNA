import SystemE
import Helpers.Pasch
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_47_step8_ahBF
    (a b h : Point) (BF : Line)
    (hbBF : b.onLine BF) (haoffBF : ¬a.onLine BF) (hbah : between b a h) :
    a.sameSide h BF := by
  euclid_apply (Elements.sameSide_of_between b a h BF)
  euclid_finish

end Elements.Book1

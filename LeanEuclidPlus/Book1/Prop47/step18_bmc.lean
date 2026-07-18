import SystemE
import Helpers.Pasch
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_47_step18_bmc
    (b c m : Point) (AL BC : Line)
    (hmAL : m.onLine AL) (hmBC : m.onLine BC)
    (hbBC : b.onLine BC) (hcBC : c.onLine BC)
    (hALBC : AL ≠ BC) (hbm : b ≠ m) (hcm : c ≠ m) (hbc : b ≠ c)
    (hbcAL : ¬b.sameSide c AL) :
    between b m c := by
  euclid_apply (Elements.between_of_not_sameSide b m c AL BC hALBC hmAL hmBC hbBC hcBC hbm hcm hbc hbcAL)

end Elements.Book1

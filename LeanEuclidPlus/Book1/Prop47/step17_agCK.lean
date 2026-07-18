import SystemE
import Helpers.Pasch
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_47_step17_agCK
    (a c g : Point) (CK : Line)
    (hcCK : c.onLine CK) (haoffCK : ¬a.onLine CK) (hcag : between c a g) :
    a.sameSide g CK := by
  euclid_apply (Elements.sameSide_of_between c a g CK)
  euclid_finish

end Elements.Book1

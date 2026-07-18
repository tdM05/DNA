import SystemE
import Helpers.SameSide
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_47_step13_par
    (b d l m : Point) (AL BD BC DE : Line)
    (hmAL : m.onLine AL) (hlAL : l.onLine AL)
    (hbBD : b.onLine BD) (hdBD : d.onLine BD)
    (hmBC : m.onLine BC) (hbBC : b.onLine BC)
    (hlDE : l.onLine DE) (hdDE : d.onLine DE)
    (hALBD : ¬AL.intersectsLine BD) (hDEBC : ¬DE.intersectsLine BC)
    (hld : l ≠ d) (hBCDE : BC ≠ DE) :
    formParallelogram m l b d AL BD BC DE := by
  have hmbDE : m.sameSide b DE := by
    euclid_apply (Elements.sameSide_of_parallel_both m b BC DE hmBC hbBC hBCDE (by euclid_finish))
  euclid_finish

end Elements.Book1

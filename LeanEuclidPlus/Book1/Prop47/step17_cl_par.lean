import SystemE
import Helpers.SameSide
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_47_step17_cl_par
    (c e l m : Point) (AL CE BC DE : Line)
    (hmAL : m.onLine AL) (hlAL : l.onLine AL)
    (hcCE : c.onLine CE) (heCE : e.onLine CE)
    (hmBC : m.onLine BC) (hcBC : c.onLine BC)
    (hlDE : l.onLine DE) (heDE : e.onLine DE)
    (hALCE : ¬AL.intersectsLine CE) (hDEBC : ¬DE.intersectsLine BC)
    (hle : l ≠ e) (hBCDE : BC ≠ DE) :
    formParallelogram m l c e AL CE BC DE := by
  have hmcDE : m.sameSide c DE := by
    euclid_apply (Elements.sameSide_of_parallel_both m c BC DE hmBC hcBC hBCDE (by euclid_finish))
  euclid_finish

end Elements.Book1

import SystemE
import Helpers.SameSide
import Helpers.Pasch
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_47_step17_B
    (a b d e l : Point) (CE AL DE : Line)
    (haAL : a.onLine AL) (hlAL : l.onLine AL)
    (hdDE : d.onLine DE) (heDE : e.onLine DE) (hlDE : l.onLine DE)
    (heCE : e.onLine CE)
    (hALCE : ¬AL.intersectsLine CE) (haoffCE : ¬a.onLine CE)
    (hdbCE : d.sameSide b CE) (hdle : between d l e) :
    a.sameSide b CE := by
  have hALCE_ne : AL ≠ CE := fun h => haoffCE (h ▸ haAL)
  have hloffCE : ¬l.onLine CE := by
    intro hlCE
    euclid_apply (intersection_lines_common_point l AL CE)
    euclid_finish
  have hedl : between e l d := by euclid_finish
  euclid_apply (Elements.sameSide_of_parallel_both a l AL CE haAL hlAL hALCE_ne hALCE)
  euclid_apply (Elements.sameSide_of_between e l d CE heCE hloffCE hedl)
  euclid_finish

end Elements.Book1

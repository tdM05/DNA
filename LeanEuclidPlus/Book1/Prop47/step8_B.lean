import SystemE
import Helpers.SameSide
import Helpers.Pasch
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_47_step8_B
    (a b c d e l : Point) (BD AL CE DE : Line)
    (haAL : a.onLine AL) (hlAL : l.onLine AL)
    (hdDE : d.onLine DE) (heDE : e.onLine DE) (hlDE : l.onLine DE)
    (hdBD : d.onLine BD) (hbBD : b.onLine BD)
    (heCE : e.onLine CE) (hcCE : c.onLine CE)
    (hALBD : ¬AL.intersectsLine BD) (haoffBD : ¬a.onLine BD)
    (hecBD : e.sameSide c BD) (hdle : between d l e) :
    a.sameSide c BD := by
  have hALBD_ne : AL ≠ BD := fun h => haoffBD (h ▸ haAL)
  have hloffBD : ¬l.onLine BD := by
    intro hlBD
    euclid_apply (intersection_lines_common_point l AL BD)
    euclid_finish
  euclid_apply (Elements.sameSide_of_parallel_both a l AL BD haAL hlAL hALBD_ne hALBD)
  euclid_apply (Elements.sameSide_of_between d l e BD hdBD hloffBD hdle)
  euclid_finish

end Elements.Book1

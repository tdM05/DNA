import SystemE
import Helpers.SameSide
import Helpers.Pasch
import Helpers.Parallel
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_47_step8_dle
    (a b c d e l : Point) (AL BD CE DE : Line)
    (haAL : a.onLine AL) (hlAL : l.onLine AL) (hlDE : l.onLine DE)
    (hdDE : d.onLine DE) (heDE : e.onLine DE)
    (hdBD : d.onLine BD) (hbBD : b.onLine BD)
    (heCE : e.onLine CE) (hcCE : c.onLine CE)
    (hALBD : ¬AL.intersectsLine BD) (hBDCE : ¬BD.intersectsLine CE)
    (haoffBD : ¬a.onLine BD) (hdbCE : d.sameSide b CE) (hcbAL : ¬b.sameSide c AL)
    (hdl : d ≠ l) (hel : e ≠ l) (hde : d ≠ e) (hALDE : AL ≠ DE) :
    between d l e := by
  have hALBD_ne : AL ≠ BD := fun h => haoffBD (h ▸ haAL)
  have hBDCE_ne : BD ≠ CE := by
    intro h; rw [h] at hdBD; euclid_finish
  have hALCE_ne : AL ≠ CE := by
    intro h; rw [← h] at heCE hcCE; euclid_finish
  have hALCE : ¬AL.intersectsLine CE := by
    euclid_apply (Elements.not_intersects_trans AL BD CE)
    euclid_finish
  have hdbAL : d.sameSide b AL := by
    euclid_apply (Elements.sameSide_of_parallel_both d b BD AL hdBD hbBD (Ne.symm hALBD_ne) (by euclid_finish))
  have hecAL : e.sameSide c AL := by
    euclid_apply (Elements.sameSide_of_parallel_both e c CE AL heCE hcCE (Ne.symm hALCE_ne) (by euclid_finish))
  have hdeAL : ¬d.sameSide e AL := by euclid_finish
  euclid_apply (Elements.between_of_not_sameSide d l e AL DE)
  euclid_finish

end Elements.Book1

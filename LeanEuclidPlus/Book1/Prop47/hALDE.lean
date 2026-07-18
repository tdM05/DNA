import SystemE
import Book1.Prop47.hALDE_dAL
import Book1.Prop47.hALDE_neq
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_47_hALDE
    (a b d e : Point) (AL DE BD CE : Line)
    (haAL : a.onLine AL) (hALBD : ¬AL.intersectsLine BD)
    (hoffBD : ¬a.onLine BD)
    (hdDE : d.onLine DE) (heDE : e.onLine DE)
    (hdBD : d.onLine BD) (hbBD : b.onLine BD)
    (heCE : e.onLine CE) (hBDCE : ¬BD.intersectsLine CE)
    (hdsCE : d.sameSide b CE)
    (hbde : ∠ b:d:e = ∟) :
    AL.intersectsLine DE := by
  by_contra hni
  have hALDE_dAL : ¬d.onLine AL := by euclid_apply (helper_1_47_hALDE_dAL a d AL BD (by euclid_assumption "" (show a.onLine AL; assumption)) (by euclid_assumption "" (show ¬AL.intersectsLine BD; assumption)) (by euclid_assumption "" (show ¬a.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)))
  have hALDE_neq : DE ≠ BD := by euclid_apply (helper_1_47_hALDE_neq b d e DE BD CE (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine CE; assumption)) (by euclid_assumption "" (show ¬BD.intersectsLine CE; assumption)) (by euclid_assumption "" (show d.sameSide b CE; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)))
  euclid_apply (parallel_line_unique d AL DE BD)
  euclid_finish

end Elements.Book1

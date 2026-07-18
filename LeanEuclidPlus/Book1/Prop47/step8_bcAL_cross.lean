import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_47_step8_bcAL_cross
    (a b d : Point) (AL BD BC : Line)
    (haAL : a.onLine AL) (hALBD : ¬AL.intersectsLine BD)
    (hbBD : b.onLine BD) (hbBC : b.onLine BC)
    (haoffBD : ¬a.onLine BD) (haoffBC : ¬a.onLine BC) (hBDBC : BD ≠ BC) :
    AL.intersectsLine BC := by
  by_contra hni
  have hALBD_ne : AL ≠ BD := fun h => haoffBD (h ▸ haAL)
  have hboffAL : ¬b.onLine AL := by
    intro hbAL
    euclid_apply (intersection_lines_common_point b AL BD)
    euclid_finish
  euclid_apply (parallel_line_unique b AL BD BC)
  euclid_finish

end Elements.Book1

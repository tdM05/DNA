import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_47_hALDE_dAL
    (a d : Point) (AL BD : Line)
    (haAL : a.onLine AL) (hALBD : ¬AL.intersectsLine BD)
    (hoffBD : ¬a.onLine BD) (hdBD : d.onLine BD) :
    ¬d.onLine AL := by
  have hne : AL ≠ BD := fun h => hoffBD (h ▸ haAL)
  intro hd
  euclid_apply (intersection_lines_common_point d AL BD)
  euclid_finish

end Elements.Book1

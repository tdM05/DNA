import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_47_s17_x7
    (a d e : Point) (BC DE : Line)
    (hd_DE : d.onLine DE) (he_DE : e.onLine DE)
    (h_nDEBC : ¬DE.intersectsLine BC)
    (hd_nBC : ¬d.onLine BC) (he_nBC : ¬e.onLine BC) (ha_nBC : ¬a.onLine BC)
    (h_nd_same_a_BC : ¬d.sameSide a BC) :
    ¬e.sameSide a BC := by
  have hed : e.sameSide d BC := by
    by_contra hcon
    euclid_apply (intersection_lines_opposing e d BC DE)
    euclid_finish
  euclid_finish

end Elements.Book1

import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_47_s8_x1
    (a b c d : Point) (AB BC BD : Line)
    (hb_BD : b.onLine BD) (hb_BC : b.onLine BC) (hb_AB : b.onLine AB)
    (hd_BD : d.onLine BD) (hc_BC : c.onLine BC) (ha_AB : a.onLine AB)
    (hbd : b ≠ d)
    (h_a_nBC : ¬a.onLine BC) (h_nd_same_a_BC : ¬d.sameSide a BC)
    (h_aSameC_BD : a.sameSide c BD) :
    d.sameSide c AB := by
  euclid_apply (triple_incidence_2 BD BC AB b d c a)
  euclid_finish

end Elements.Book1

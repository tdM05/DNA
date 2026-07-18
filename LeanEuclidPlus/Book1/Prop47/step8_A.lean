import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_47_step8_A
    (a b c d : Point) (BD BC AB : Line)
    (hbBD : b.onLine BD) (hdBD : d.onLine BD)
    (hbBC : b.onLine BC) (hcBC : c.onLine BC)
    (hbAB : b.onLine AB) (haAB : a.onLine AB)
    (hacBD : a.sameSide c BD) (hdaBC : ¬d.sameSide a BC)
    (haoffBC : ¬a.onLine BC) (hdb : d ≠ b) :
    d.sameSide c AB := by
  euclid_apply (triple_incidence_2 BD BC AB b d c a)
  euclid_finish

end Elements.Book1

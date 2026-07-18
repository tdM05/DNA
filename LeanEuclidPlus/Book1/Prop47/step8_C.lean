import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_47_step8_C
    (a b c f : Point) (BF AB BC : Line)
    (hbBF : b.onLine BF) (hfBF : f.onLine BF)
    (hbAB : b.onLine AB) (haAB : a.onLine AB)
    (hbBC : b.onLine BC) (hcBC : c.onLine BC)
    (hcaBF : c.sameSide a BF) (hfcAB : ¬f.sameSide c AB)
    (hcoffAB : ¬c.onLine AB) (hfb : f ≠ b) :
    f.sameSide a BC := by
  euclid_apply (triple_incidence_2 BF AB BC b f a c)
  euclid_finish

end Elements.Book1

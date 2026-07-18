import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_47_step20_gb_par
    (a b f g : Point) (GF AB AG BF : Line)
    (hgGF : g.onLine GF) (hfGF : f.onLine GF)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hgAG : g.onLine AG) (haAG : a.onLine AG)
    (hfBF : f.onLine BF) (hbBF : b.onLine BF) (hfb : f ≠ b)
    (hgaBF : g.sameSide a BF)
    (hGFAB : ¬GF.intersectsLine AB) (hAGBF : ¬AG.intersectsLine BF) :
    formParallelogram g f a b GF AB AG BF := by
  euclid_finish

end Elements.Book1

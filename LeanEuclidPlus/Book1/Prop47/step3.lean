import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_47_step3
    (a c d f g : Point) (AD FC BC AB GF : Line)
    (haAD : a.onLine AD) (hdAD : d.onLine AD)
    (hfFC : f.onLine FC) (hcFC : c.onLine FC)
    (hdopp : ¬d.sameSide a BC) (haoffBC : ¬a.onLine BC)
    (hgc : ¬g.sameSide c AB) (hgGF : g.onLine GF) (hfGF : f.onLine GF)
    (hGFAB : ¬GF.intersectsLine AB) (hcoffAB : ¬c.onLine AB) (haAB : a.onLine AB)
    (hgoffAB : ¬g.onLine AB) :
    distinctPointsOnLine a d AD ∧ distinctPointsOnLine f c FC := by
  euclid_finish

end Elements.Book1

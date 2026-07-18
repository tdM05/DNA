import SystemE
import Helpers.SameSide
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_47_step8_gfAB
    (f g : Point) (GF AB : Line)
    (hgGF : g.onLine GF) (hfGF : f.onLine GF)
    (hgoffAB : ¬g.onLine AB) (hGFAB : ¬GF.intersectsLine AB) :
    g.sameSide f AB := by
  euclid_apply (Elements.sameSide_of_parallel' g f g GF AB)
  euclid_finish

end Elements.Book1

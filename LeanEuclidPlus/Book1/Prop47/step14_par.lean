import SystemE
import Helpers.SameSide
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_47_step14_par
    (a b c f g : Point) (AC BF GF AB : Line)
    (hcAC : c.onLine AC) (haAC : a.onLine AC)
    (hfBF : f.onLine BF) (hbBF : b.onLine BF)
    (hgGF : g.onLine GF) (hfGF : f.onLine GF)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hcag : between c a g) (hgoffAB : ¬g.onLine AB)
    (hACBF : ¬AC.intersectsLine BF) (hGFAB : ¬GF.intersectsLine AB)
    (hab : a ≠ b) :
    formParallelogram g a f b AC BF GF AB := by
  have hgAC : g.onLine AC := by euclid_finish
  have hgfAB : g.sameSide f AB := by
    euclid_apply (Elements.sameSide_of_parallel' g f g GF AB hgGF hfGF hgGF hgoffAB hGFAB)
  euclid_finish

end Elements.Book1

import SystemE
import Book1.Prop17.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3
open Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_3_25_hint3 (a b c d e0p : Point) (AC DB AB AE : Line)
    (hAa : a.onLine AC) (hAc : c.onLine AC) (hac : a ≠ c) (hbAC : ¬b.onLine AC)
    (hadc : between a d c) (hdDB : d.onLine DB) (hbDB : b.onLine DB)
    (hstep2 : ∠ a:d:b = ∟) (haAB : a.onLine AB) (hbAB : b.onLine AB) (hab : a ≠ b)
    (he0p_ang : ∠ e0p:a:b = ∠ a:b:d) (he0p_side : e0p.sameSide d AB)
    (haAE : a.onLine AE) (he0pAE : e0p.onLine AE) : AE.intersectsLine DB := by
  euclid_apply (proposition_17 a d b AC DB AB)
  euclid_apply (lines_intersect e0p a b d AE AB DB) as eW
  euclid_apply (intersection_lines_common_point eW AE DB)
  euclid_finish

end Elements.Book3

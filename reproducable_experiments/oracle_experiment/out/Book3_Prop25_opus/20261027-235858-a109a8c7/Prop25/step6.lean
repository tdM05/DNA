import SystemE
import Book1.Prop17.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3
open Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_3_25_step6 (a b c d e e0p : Point) (AC DB AB AE : Line)
    (hAa : a.onLine AC) (hAc : c.onLine AC) (hac : a ≠ c) (hbAC : ¬b.onLine AC)
    (hadc : between a d c) (hdDB : d.onLine DB) (hbDB : b.onLine DB)
    (hstep2 : ∠ a:d:b = ∟) (haAB : a.onLine AB) (hbAB : b.onLine AB) (hab : a ≠ b)
    (he0p_ang : ∠ e0p:a:b = ∠ a:b:d) (he0p_side : e0p.sameSide d AB)
    (haAE : a.onLine AE) (he0pAE : e0p.onLine AE)
    (heAE : e.onLine AE) (heDB : e.onLine DB) : ∠ b:a:e = ∠ a:b:d := by
  -- e lies on the unique meet of AE and DB, on e0p's side of AB, so it is on ray a→e0p.
  euclid_apply (proposition_17 a d b AC DB AB)
  euclid_apply (lines_intersect e0p a b d AE AB DB) as eW
  euclid_finish

end Elements.Book3

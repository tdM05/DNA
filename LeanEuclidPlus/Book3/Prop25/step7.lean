import SystemE
import Book1.Prop17.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3
open Elements.Book1

theorem helper_3_25_step7 (a b c d e e0p : Point) (AC DB AB AE : Line)
    (hAa : a.onLine AC) (hAc : c.onLine AC) (hac : a ≠ c) (hbAC : ¬b.onLine AC)
    (hadc : between a d c) (hdDB : d.onLine DB) (hbDB : b.onLine DB)
    (hstep2 : ∠ a:d:b = ∟) (haAB : a.onLine AB) (hbAB : b.onLine AB) (hab : a ≠ b)
    (he0p_ang : ∠ e0p:a:b = ∠ a:b:d)
    (he0p_side : e0p.sameSide d AB) (haAE : a.onLine AE) (he0pAE : e0p.onLine AE)
    (heAE : e.onLine AE) (heDB : e.onLine DB)
    (hgt : ∠ a:b:d > ∠ b:a:d) (hstep6 : ∠ b:a:e = ∠ a:b:d) : between b d e := by
  -- e is the unique meet of AE and DB; lines_intersect places it on e0p's (= d's) side of AB.
  euclid_apply (proposition_17 a d b AC DB AB)
  euclid_apply (lines_intersect e0p a b d AE AB DB) as eW
  have hesd : e.sameSide d AB := by euclid_finish
  -- e ∉ AC (else e = AC∩DB = d, but ∠b:a:e > ∠b:a:d forces e ≠ d).
  have hedne : e ≠ d := by euclid_finish
  have heAC : ¬ e.onLine AC := by euclid_finish
  -- If b and e were on the same side of AC, angle addition would give ∠b:a:d ≥ ∠b:a:e — impossible.
  have hopp : ¬ b.sameSide e AC := by
    intro hcon
    euclid_apply (sum_angles_onlyif a b d e AB AC)
    euclid_finish
  euclid_apply (pasch_4 b d e AC DB)
  euclid_finish

end Elements.Book3

import SystemE
import Book1.Prop17.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3
open Elements.Book1

theorem helper_3_25_step22 (a b c d e e0p : Point) (AC DB AB AE : Line)
    (hAa : a.onLine AC) (hAc : c.onLine AC) (hac : a ≠ c) (hbAC : ¬b.onLine AC)
    (hadc : between a d c) (hdDB : d.onLine DB) (hbDB : b.onLine DB)
    (hstep2 : ∠ a:d:b = ∟) (haAB : a.onLine AB) (hbAB : b.onLine AB) (hab : a ≠ b)
    (he0p_ang : ∠ e0p:a:b = ∠ a:b:d) (he0p_side : e0p.sameSide d AB)
    (haAE : a.onLine AE) (he0pAE : e0p.onLine AE) (heAE : e.onLine AE) (heDB : e.onLine DB)
    (hlt : ∠ a:b:d < ∠ b:a:d) (hstep21b : ∠ b:a:e = ∠ a:b:d) : e.sameSide b AC := by
  -- ∠BAE = ∠ABD < ∠BAD, so ray AE stays inside angle BAD — E is on B's side of AC.
  euclid_apply (proposition_17 a d b AC DB AB)
  euclid_apply (lines_intersect e0p a b d AE AB DB) as eW
  have hesd : e.sameSide d AB := by euclid_finish
  have hdAC : d.onLine AC := by euclid_finish
  have heAC : ¬ e.onLine AC := by
    intro hc
    euclid_apply (two_points_determine_line d e DB AC)
    euclid_finish
  by_contra hcon
  -- Otherwise b and e are on opposite sides of AC, so d is between b and e.
  euclid_apply (pasch_4 b d e AC DB)
  -- Then ray AD splits ∠BAE, giving ∠BAE = ∠BAD + ∠DAE > ∠BAD — contradicting ∠BAE = ∠ABD < ∠BAD.
  euclid_apply (sum_angles_onlyif a b e d AB AE)
  euclid_finish

end Elements.Book3

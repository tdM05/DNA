import SystemE
import Book1.Prop17.Main
import Helpers.Angle
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1
open Elements

theorem helper_3_25_hEb_bae (a b c d e g3 : Point) (AC DB AB AG3 : Line)
    (haAC : a.onLine AC) (hcAC : c.onLine AC) (hac : a ≠ c) (hboff : ¬b.onLine AC)
    (hadc : between a d c)
    (hdDB : d.onLine DB) (hbDB : b.onLine DB) (heDB : e.onLine DB)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hab : a ≠ b)
    (hadbperp : ∠ a:d:b = ∟)
    (hg3a : g3 ≠ a) (hg3side : g3.onLine AB ∨ g3.sameSide d AB)
    (hg3ab : ∠ g3:a:b = ∠ a:b:d)
    (haAG3 : a.onLine AG3) (hg3AG3 : g3.onLine AG3) (heAG3 : e.onLine AG3)
    (hlt : ∠ a:b:d < ∠ b:a:d)
    (step22 : e.onLine DB ∧ e.sameSide b AC) (step23 : b.sameSide e AC) :
    ∠ b:a:e = ∠ a:b:d := by
  obtain ⟨_, hesb⟩ := step22
  rcases hg3side with hg3AB | hg3ss
  · -- g3 on AB ⟹ ∠ g3:a:b = ∠ a:b:d ∈ (0, ∟), impossible for collinear a,b,g3
    exfalso
    euclid_apply (proposition_17 a b d AB DB AC)
    euclid_finish
  · -- g3 strictly off AB on d's side.  e lies on line AG3 through a; either e is on
    -- ray a→g3 (¬between g3 a e), giving ∠ b:a:e = ∠ b:a:g3 = ∠ a:b:d directly, or
    -- a is between g3 and e, impossible for the perpendicular figure.
    by_cases hbtw : between g3 a e
    · exfalso
      euclid_apply (proposition_17 a b d AB DB AC)
      euclid_apply (proposition_17 e a d AG3 AC DB)
      euclid_apply (angle_split a b g3 d AB AG3)
      euclid_finish
    · euclid_apply (equal_angles a b b e g3 AB AG3)
      euclid_finish

end Elements.Book3

import SystemE
import Book1.Prop17.Main
import Helpers.Angle
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1
open Elements

theorem helper_3_25_step6 (a b c d e g : Point) (AC DB AB AG : Line)
    (haAC : a.onLine AC) (hcAC : c.onLine AC) (hac : a ≠ c) (hboff : ¬b.onLine AC)
    (habcb : |(a─b)| = |(c─b)|)
    (hadc : between a d c) (haddc : |(a─d)| = |(d─c)|)
    (hdDB : d.onLine DB) (hbDB : b.onLine DB)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hab : a ≠ b)
    (hadbperp : ∠ a:d:b = ∟)
    (hgt : ∠ a:b:d > ∠ b:a:d)
    (hga : g ≠ a) (hgside : g.onLine AB ∨ g.sameSide d AB)
    (hgab : ∠ g:a:b = ∠ a:b:d)
    (haAG : a.onLine AG) (hgAG : g.onLine AG) (hAGDB : AG.intersectsLine DB)
    (heAG : e.onLine AG) (heDB : e.onLine DB) :
    ∠ b:a:e = ∠ a:b:d ∧ e ≠ a := by
  have hea : e ≠ a := by euclid_finish
  refine ⟨?_, hea⟩
  rcases hgside with hgAB | hgss
  · -- g on AB ⟹ ∠ g:a:b = ∠ a:b:d ∈ (0, ∟), impossible for collinear a,b,g
    exfalso
    euclid_apply (proposition_17 a b d AB DB AC)
    euclid_finish
  · -- g strictly off AB on d's side.  e lies on line AG through a; either e is on
    -- ray a→g (¬between g a e), giving ∠ b:a:e = ∠ b:a:g = ∠ a:b:d directly, or
    -- a is between g and e, which is impossible for the perpendicular figure.
    by_cases hbtw : between g a e
    · exfalso
      -- ∠ a:b:d < ∟  (right triangle a b d, right angle at d)
      euclid_apply (proposition_17 a b d AB DB AC)
      -- ∠ e:a:d < ∟  (right triangle e a d, right angle at d)
      euclid_apply (proposition_17 e a d AG AC DB)
      -- ∠ b:a:g = ∠ b:a:d + ∠ d:a:g  (ray a→d lies inside ∠ b:a:g)
      euclid_apply (angle_split a b g d AB AG)
      euclid_finish
    · euclid_apply (equal_angles a b b e g AB AG)
      euclid_finish

end Elements.Book3

import SystemE
import Book1.Prop17.Main
import Helpers.Angle
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1
open Elements

theorem helper_3_25_step9_assumption1 (a b c d e g : Point) (AC DB AB AG : Line)
    (haAC : a.onLine AC) (hcAC : c.onLine AC) (hac : a ≠ c) (hboff : ¬b.onLine AC)
    (hadc : between a d c) (haddc : |(a─d)| = |(d─c)|)
    (hdDB : d.onLine DB) (hbDB : b.onLine DB)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hab : a ≠ b)
    (hadbperp : ∠ a:d:b = ∟)
    (hgt : ∠ a:b:d > ∠ b:a:d)
    (hga : g ≠ a) (hgside : g.onLine AB ∨ g.sameSide d AB)
    (hgab : ∠ g:a:b = ∠ a:b:d)
    (haAG : a.onLine AG) (hgAG : g.onLine AG) (hAGDB : AG.intersectsLine DB)
    (heAG : e.onLine AG) (heDB : e.onLine DB)
    (hstep6 : ∠ b:a:e = ∠ a:b:d ∧ e ≠ a) :
    ∠ a:b:e = ∠ b:a:e := by
  obtain ⟨hbae, hea⟩ := hstep6
  rcases hgside with hgAB | hgss
  · exfalso
    euclid_apply (proposition_17 a b d AB DB AC)
    euclid_finish
  · have hng : ¬ between g a e := by
      by_cases h : between g a e
      · exfalso
        euclid_apply (proposition_17 a b d AB DB AC)
        euclid_apply (proposition_17 e a d AG AC DB)
        euclid_apply (angle_split a b g d AB AG)
        euclid_finish
      · exact h
    have hbde : between b d e := by euclid_finish
    euclid_apply (equal_angles b a a e d AB DB)
    euclid_finish

end Elements.Book3

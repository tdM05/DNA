import SystemE
import Book1.Prop17.Main
import Helpers.Angle
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1
open Elements

theorem helper_3_25_hEb_abe (a b c d e g3 : Point) (AC DB AB AG3 : Line)
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
    ∠ a:b:e = ∠ a:b:d := by
  obtain ⟨_, hesb⟩ := step22
  rcases hg3side with hg3AB | hg3ss
  · exfalso
    euclid_apply (proposition_17 a b d AB DB AC)
    euclid_finish
  · -- e is on ray a→g3 (¬ between g3 a e), so e lies between d and b on DB
    have hng : ¬ between g3 a e := by
      by_cases h : between g3 a e
      · exfalso
        euclid_apply (proposition_17 a b d AB DB AC)
        euclid_apply (proposition_17 e a d AG3 AC DB)
        euclid_apply (angle_split a b g3 d AB AG3)
        euclid_finish
      · exact h
    have hdeb : between d e b := by euclid_finish
    euclid_apply (equal_angles b a a e d AB DB)
    euclid_finish

end Elements.Book3

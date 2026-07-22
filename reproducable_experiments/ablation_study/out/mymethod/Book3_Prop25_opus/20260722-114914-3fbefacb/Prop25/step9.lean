import SystemE
import Book1.Prop17.Main
import Book1.Prop06.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1
open Elements

theorem helper_3_25_step9 (a b c d e g : Point) (AC DB AB AG : Line)
    (haAC : a.onLine AC) (hcAC : c.onLine AC) (hboff : ¬b.onLine AC)
    (hadc : between a d c)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hab : a ≠ b)
    (hadbperp : ∠ a:d:b = ∟)
    (hgt : ∠ a:b:d > ∠ b:a:d)
    (hga : g ≠ a) (hgside : g.onLine AB ∨ g.sameSide d AB)
    (hgab : ∠ g:a:b = ∠ a:b:d)
    (haAG : a.onLine AG) (hgAG : g.onLine AG)
    (hdDB : d.onLine DB) (hbDB : b.onLine DB)
    (heAG : e.onLine AG) (heDB : e.onLine DB)
    (hstep6 : ∠ b:a:e = ∠ a:b:d ∧ e ≠ a)
    (hasm : ∠ a:b:e = ∠ b:a:e) :
    |(e─b)| = |(e─a)| := by
  obtain ⟨_, hea⟩ := hstep6
  have heoffAB : ¬ e.onLine AB := by
    rcases hgside with hgAB | hgss
    · exfalso
      euclid_apply (proposition_17 a b d AB DB AC)
      euclid_finish
    · intro heAB
      euclid_apply (two_points_determine_line a e AB AG)
      euclid_finish
  euclid_apply (proposition_6 e a b AG AB DB)
  euclid_finish

end Elements.Book3

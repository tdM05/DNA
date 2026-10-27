import SystemE
import Book1.Prop06.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_step9 (a b c d g e : Point) (AC DB AB AG : Line)
    (haAC : a.onLine AC) (hcAC : c.onLine AC) (hbAC : ¬b.onLine AC)
    (hbet : between a d c)
    (hdDB : d.onLine DB) (hbDB : b.onLine DB)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hperp : ∠ a:d:b = ∟)
    (hgt : ∠ a:b:d > ∠ b:a:d)
    (hga : g ≠ a) (hab_ne : a ≠ b) (hg_side : g.onLine AB ∨ g.sameSide d AB)
    (hgab : ∠ g:a:b = ∠ a:b:d)
    (haAG : a.onLine AG) (hgAG : g.onLine AG)
    (heAG : e.onLine AG) (heDB : e.onLine DB)
    (hstep6 : ∠ b:a:e = ∠ a:b:d ∧ e ≠ a)
    (hstep9a1 : ∠ a:b:e = ∠ b:a:e) :
    |(e─b)| = |(e─a)| := by
  obtain ⟨_, hea⟩ := hstep6
  have hgside : g.sameSide d AB := by euclid_finish
  have heAB : ¬ e.onLine AB := by euclid_finish
  euclid_apply (Elements.Book1.proposition_6 e a b AG AB DB)
  euclid_finish

end Elements.Book3

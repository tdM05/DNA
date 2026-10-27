import SystemE
import Book1.Prop17.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_step12_tri1 (a b c d e g : Point) (AC DB AB AG : Line)
    (haAC : a.onLine AC) (hcAC : c.onLine AC) (hbAC : ¬b.onLine AC)
    (hbet : between a d c)
    (hdDB : d.onLine DB) (hbDB : b.onLine DB) (heDB : e.onLine DB)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hperp : ∠ a:d:b = ∟) (hgt : ∠ a:b:d > ∠ b:a:d)
    (hga : g ≠ a) (hab_ne : a ≠ b) (hg_side : g.onLine AB ∨ g.sameSide d AB)
    (hgab : ∠ g:a:b = ∠ a:b:d)
    (haAG : a.onLine AG) (hgAG : g.onLine AG) (heAG : e.onLine AG)
    (hstep6 : ∠ b:a:e = ∠ a:b:d ∧ e ≠ a) :
    formTriangle d a e AC AG DB := by
  obtain ⟨_, hea⟩ := hstep6
  have hgside : g.sameSide d AB := by euclid_finish
  euclid_apply (Elements.Book1.proposition_17 a b d AB DB AC)
  have hgoffAC : ¬ g.onLine AC := by euclid_finish
  have hed : e ≠ d := by euclid_finish
  euclid_finish

end Elements.Book3

import SystemE
import Book1.Prop17.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_step9_assumption1 (a b c d e g : Point) (AC DB AB AG : Line)
    (haAC : a.onLine AC) (hcAC : c.onLine AC) (hac : a ≠ c) (hbAC : ¬b.onLine AC)
    (hbet : between a d c) (had_dc : |(a─d)| = |(d─c)|)
    (hdDB : d.onLine DB) (hbDB : b.onLine DB) (heDB : e.onLine DB)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hab : a ≠ b)
    (haAG : a.onLine AG) (heAG : e.onLine AG)
    (hga : g ≠ a) (hgAG : g.onLine AG)
    (hgAB : g.onLine AB ∨ g.sameSide d AB) (hgab : ∠ g:a:b = ∠ a:b:d)
    (hadb : ∠ a:d:b = ∟) (hgt : ∠ a:b:d > ∠ b:a:d)
    (hstep6 : ∠ b:a:e = ∠ a:b:d ∧ e ≠ a) :
    ∠ a:b:e = ∠ b:a:e := by
  obtain ⟨hbae, hea⟩ := hstep6
  -- ∠abd < ∟ (right triangle abd), g on d's side of AB.
  euclid_apply (Elements.Book1.proposition_17 a b d AB DB AC)
  have hgsd : g.sameSide d AB := by
    rcases hgAB with h | h
    · exfalso; euclid_finish
    · exact h
  -- e is on ray AG (g's side of AB), and since ∠bae = ∠abd > ∠bad, ray AE lies beyond AC:
  -- e is on the opposite side of AC from b, so DB crosses AC at d between b and e.
  euclid_assert e.sameSide g AB
  euclid_assert e.opposingSides b AC
  euclid_assert between b d e
  -- ray be = ray bd, so ∠abe = ∠abd = ∠bae.
  euclid_finish

end Elements.Book3

import SystemE
import Book1.Prop17.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_step22 (a b c d e g3 : Point) (AC DB AB AG3 : Line)
    (haAC : a.onLine AC) (hcAC : c.onLine AC) (hac : a ≠ c) (hbAC : ¬b.onLine AC)
    (hbet : between a d c)
    (hdDB : d.onLine DB) (hbDB : b.onLine DB) (heDB : e.onLine DB)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hab : a ≠ b)
    (haAG3 : a.onLine AG3) (heAG3 : e.onLine AG3)
    (hga : g3 ≠ a) (hgAG3 : g3.onLine AG3)
    (hgAB : g3.onLine AB ∨ g3.sameSide d AB) (hgab : ∠ g3:a:b = ∠ a:b:d)
    (hadb : ∠ a:d:b = ∟)
    (hlt : ∠ a:b:d < ∠ b:a:d) :
    e.onLine DB ∧ e.sameSide b AC := by
  -- ∠abd < ∟, g3 on d's side of AB; since ∠g3ab = ∠abd < ∠bad, ray AG3 lies between AB and AC,
  -- so e (on AG3) is on the same side of AC as b.
  euclid_apply (Elements.Book1.proposition_17 a b d AB DB AC)
  have hgsd : g3.sameSide d AB := by
    rcases hgAB with h | h
    · exfalso; euclid_finish
    · exact h
  euclid_assert e.sameSide g3 AB
  euclid_assert e.sameSide b AC
  euclid_finish

end Elements.Book3

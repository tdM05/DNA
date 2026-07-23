import SystemE
import Book1.Prop06.Main
import Book1.Prop17.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_step9 (a b c d e g : Point) (AC DB AB AG : Line)
    (haAC : a.onLine AC) (hcAC : c.onLine AC) (hac : a ≠ c) (hbAC : ¬b.onLine AC)
    (hbet : between a d c)
    (hdDB : d.onLine DB) (hbDB : b.onLine DB) (heDB : e.onLine DB)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hab : a ≠ b)
    (haAG : a.onLine AG) (heAG : e.onLine AG)
    (hga : g ≠ a) (hgAG : g.onLine AG)
    (hgAB : g.onLine AB ∨ g.sameSide d AB) (hgab : ∠ g:a:b = ∠ a:b:d)
    (hadb : ∠ a:d:b = ∟) (hgt : ∠ a:b:d > ∠ b:a:d)
    (hangle : ∠ a:b:e = ∠ b:a:e) :
    |(e─b)| = |(e─a)| := by
  -- e lies below AC (opposite side from b), so d is between b and e ⟹ e ≠ b, a ∉ DB ⟹ triangle e a b.
  euclid_apply (Elements.Book1.proposition_17 a b d AB DB AC)
  have hgsd : g.sameSide d AB := by
    rcases hgAB with h | h
    · exfalso; euclid_finish
    · exact h
  euclid_assert e.sameSide g AB
  euclid_assert e.opposingSides b AC
  euclid_assert between b d e
  have htri : formTriangle e a b AG AB DB := by euclid_finish
  have hsym : ∠ e:a:b = ∠ e:b:a := by euclid_finish
  -- base angles ∠eab = ∠eba equal ⟹ legs ea = eb [Prop.~1.6].
  euclid_apply (Elements.Book1.proposition_6 e a b AG AB DB)
  euclid_finish

end Elements.Book3

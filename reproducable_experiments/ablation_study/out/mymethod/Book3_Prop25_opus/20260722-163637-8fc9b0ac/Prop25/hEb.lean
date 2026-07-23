import SystemE
import Book1.Prop06.Main
import Book1.Prop17.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_hEb (a b c d e g3 : Point) (AC DB AB AG3 : Line)
    (haAC : a.onLine AC) (hcAC : c.onLine AC) (hac : a ≠ c) (hbAC : ¬b.onLine AC)
    (hbet : between a d c)
    (hdDB : d.onLine DB) (hbDB : b.onLine DB) (heDB : e.onLine DB)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hab : a ≠ b)
    (haAG3 : a.onLine AG3) (heAG3 : e.onLine AG3)
    (hga : g3 ≠ a) (hgAG3 : g3.onLine AG3)
    (hgAB : g3.onLine AB ∨ g3.sameSide d AB) (hgab : ∠ g3:a:b = ∠ a:b:d)
    (hadb : ∠ a:d:b = ∟)
    (hlt : ∠ a:b:d < ∠ b:a:d)
    (hstep22 : e.onLine DB ∧ e.sameSide b AC) :
    |(e─a)| = |(e─b)| := by
  obtain ⟨heDB2, hessb⟩ := hstep22
  -- ∠abd < ∟ (right triangle abd); g3 on d's side of AB.
  euclid_apply (Elements.Book1.proposition_17 a b d AB DB AC)
  have hgsd : g3.sameSide d AB := by
    rcases hgAB with h | h
    · exfalso; euclid_finish
    · exact h
  -- e (on ray AG3) is on d's side of AB, and on b's side of AC, so it sits between d and b on DB.
  euclid_assert e.sameSide g3 AB
  euclid_assert ¬ between d b e
  -- Triangle eab with equal base angles ∠eab = ∠eba = ∠abd, so ea = eb (Prop 1.6).
  have htri : formTriangle e a b AG3 AB DB := by euclid_finish
  have hsym : ∠ e:a:b = ∠ e:b:a := by euclid_finish
  euclid_apply (Elements.Book1.proposition_6 e a b AG3 AB DB)
  euclid_finish

end Elements.Book3

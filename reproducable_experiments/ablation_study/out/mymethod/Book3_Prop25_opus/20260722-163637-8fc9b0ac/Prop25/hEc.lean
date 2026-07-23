import SystemE
import Book1.Prop04.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_hEc (a b c d e : Point) (AC DB AG3 : Line)
    (haAC : a.onLine AC) (hcAC : c.onLine AC) (hac : a ≠ c) (hbAC : ¬b.onLine AC)
    (hbet : between a d c) (had_dc : |(a─d)| = |(d─c)|)
    (hdDB : d.onLine DB) (hbDB : b.onLine DB) (heDB : e.onLine DB)
    (haAG3 : a.onLine AG3) (heAG3 : e.onLine AG3)
    (hadb : ∠ a:d:b = ∟)
    (hstep22 : e.onLine DB ∧ e.sameSide b AC) :
    |(e─a)| = |(e─c)| := by
  obtain ⟨heDB2, hessb⟩ := hstep22
  -- DB ⊥ AC at the midpoint d, and e (≠ d) lies on DB on b's side of AC.
  euclid_assert e ≠ c
  euclid_apply (line_from_points c e) as CE
  -- Both ∠ade and ∠cde are right angles (∠adb = ∟, e on b's ray from d), so they are equal.
  euclid_assert ∠ a:d:e = ∠ c:d:e
  have htri1 : formTriangle d a e AC AG3 DB := by euclid_finish
  have htri2 : formTriangle d c e AC CE DB := by euclid_finish
  -- SAS: DA = DC, DE common, ∠ADE = ∠CDE ⟹ base AE = CE [Prop.~1.4].
  euclid_apply (Elements.Book1.proposition_4 d a e d c e AC AG3 DB AC CE DB)
  euclid_finish

end Elements.Book3

import SystemE
import Book1.Prop04.Main
import Book1.Prop17.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_step12 (a b c d e g : Point) (AC DB AB AG EC : Line)
    (haAC : a.onLine AC) (hcAC : c.onLine AC) (hac : a ≠ c) (hbAC : ¬b.onLine AC)
    (hbet : between a d c)
    (hdDB : d.onLine DB) (hbDB : b.onLine DB) (heDB : e.onLine DB)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hab : a ≠ b)
    (haAG : a.onLine AG) (heAG : e.onLine AG)
    (heEC : e.onLine EC) (hcEC : c.onLine EC)
    (hga : g ≠ a) (hgAG : g.onLine AG)
    (hgAB : g.onLine AB ∨ g.sameSide d AB) (hgab : ∠ g:a:b = ∠ a:b:d)
    (hadb : ∠ a:d:b = ∟) (hgt : ∠ a:b:d > ∠ b:a:d)
    (had_dc : |(a─d)| = |(d─c)|) (hstep11 : ∠ a:d:e = ∠ c:d:e) :
    |(a─e)| = |(c─e)| := by
  -- e lies below AC (opposite side from b): d between b and e, hence e off AC ⟹ triangles dae, dce.
  euclid_apply (Elements.Book1.proposition_17 a b d AB DB AC)
  have hgsd : g.sameSide d AB := by
    rcases hgAB with h | h
    · exfalso; euclid_finish
    · exact h
  euclid_assert e.sameSide g AB
  euclid_assert e.opposingSides b AC
  euclid_assert between b d e
  have htri1 : formTriangle d a e AC AG DB := by euclid_finish
  have htri2 : formTriangle d c e AC EC DB := by euclid_finish
  -- SAS: DA = DC, DE common, ∠ADE = ∠CDE ⟹ base AE = CE [Prop.~1.4].
  euclid_apply (Elements.Book1.proposition_4 d a e d c e AC AG DB AC EC DB)
  euclid_finish

end Elements.Book3

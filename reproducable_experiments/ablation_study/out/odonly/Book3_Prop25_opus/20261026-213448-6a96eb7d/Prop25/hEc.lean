import SystemE
import Book1.Prop04.Main
import Book3.Prop25.hEc_tri1
import Book3.Prop25.hEc_tri2
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_hEc (a b c d g3 e : Point) (AC DB AB AG3 : Line)
    (haAC : a.onLine AC) (hcAC : c.onLine AC) (hac : a ≠ c) (hbAC : ¬b.onLine AC)
    (hbet : between a d c) (hadc : |(a─d)| = |(d─c)|)
    (hdDB : d.onLine DB) (hbDB : b.onLine DB) (heDB : e.onLine DB)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hperp : ∠ a:d:b = ∟)
    (hlt : ∠ a:b:d < ∠ b:a:d)
    (hg3a : g3 ≠ a) (hab_ne : a ≠ b) (hg3_side : g3.onLine AB ∨ g3.sameSide d AB)
    (hg3ab : ∠ g3:a:b = ∠ a:b:d)
    (haAG3 : a.onLine AG3) (hg3AG3 : g3.onLine AG3) (heAG3 : e.onLine AG3) :
    |(e─a)| = |(e─c)| := by
  euclid_apply (line_from_points c e) as CE
  have hEc_tri1 : formTriangle d a e AC AG3 DB := by euclid_apply (helper_3_25_hEc_tri1 a b c d g3 e AC DB AB AG3 (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show ¬b.onLine AC; assumption)) (by euclid_assumption "" (show between a d c; assumption)) (by euclid_assumption "" (show d.onLine DB; assumption)) (by euclid_assumption "" (show b.onLine DB; assumption)) (by euclid_assumption "" (show e.onLine DB; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show ∠ a:d:b = ∟; assumption)) (by euclid_assumption "" (show ∠ a:b:d < ∠ b:a:d; assumption)) (by euclid_assumption "" (show g3 ≠ a; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show g3.onLine AB ∨ g3.sameSide d AB; assumption)) (by euclid_assumption "" (show ∠ g3:a:b = ∠ a:b:d; assumption)) (by euclid_assumption "" (show a.onLine AG3; assumption)) (by euclid_assumption "" (show g3.onLine AG3; assumption)) (by euclid_assumption "" (show e.onLine AG3; assumption)))
  have hEc_tri2 : formTriangle d c e AC CE DB := by euclid_apply (helper_3_25_hEc_tri2 a b c d g3 e AC DB AB AG3 CE (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show ¬b.onLine AC; assumption)) (by euclid_assumption "" (show between a d c; assumption)) (by euclid_assumption "" (show d.onLine DB; assumption)) (by euclid_assumption "" (show b.onLine DB; assumption)) (by euclid_assumption "" (show e.onLine DB; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show ∠ a:d:b = ∟; assumption)) (by euclid_assumption "" (show ∠ a:b:d < ∠ b:a:d; assumption)) (by euclid_assumption "" (show g3 ≠ a; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show g3.onLine AB ∨ g3.sameSide d AB; assumption)) (by euclid_assumption "" (show ∠ g3:a:b = ∠ a:b:d; assumption)) (by euclid_assumption "" (show a.onLine AG3; assumption)) (by euclid_assumption "" (show g3.onLine AG3; assumption)) (by euclid_assumption "" (show e.onLine AG3; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e.onLine CE; assumption)))
  euclid_apply (Elements.Book1.proposition_4 d a e d c e AC AG3 DB AC CE DB)
  euclid_finish

end Elements.Book3

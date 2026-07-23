import SystemE
import Book1.Prop04.Main
import Book3.Prop25.step12_eoffac
import Book3.Prop25.step12_tri1
import Book3.Prop25.step12_tri2
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1

theorem helper_3_25_step12 (a b c d e g : Point) (AC AB DB AG EC : Line)
    (haAC : a.onLine AC) (hcAC : c.onLine AC) (hboff : ¬ b.onLine AC)
    (hbtw : between a d c) (hadb : ∠ a:d:b = ∟)
    (hdDB : d.onLine DB) (hbDB : b.onLine DB) (heDB : e.onLine DB)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hga : g ≠ a) (hgdisj : g.onLine AB ∨ g.sameSide d AB) (hang : ∠ g:a:b = ∠ a:b:d)
    (hgt : ∠ a:b:d > ∠ b:a:d)
    (haAG : a.onLine AG) (hgAG : g.onLine AG) (heAG : e.onLine AG)
    (hcEC : c.onLine EC) (heEC : e.onLine EC)
    (hec : e ≠ c)
    (hstep10 : |(a─d)| = |(c─d)| ∧ |(d─e)| = |(d─e)|)
    (hstep11 : ∠ a:d:e = ∠ c:d:e)
    (hrt : ∠ a:d:e = ∟ ∧ ∠ c:d:e = ∟) :
    |(a─e)| = |(c─e)| := by
  -- e is off AC (it is the AG∩DB crossing on the far side of AC from b).
  have step12_eoffac : ¬ e.onLine AC := by euclid_apply (helper_3_25_step12_eoffac a b c d e g AC AB DB AG (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show ¬ b.onLine AC; assumption)) (by euclid_assumption "" (show between a d c; assumption)) (by euclid_assumption "" (show ∠ a:d:b = ∟; assumption)) (by euclid_assumption "" (show d.onLine DB; assumption)) (by euclid_assumption "" (show b.onLine DB; assumption)) (by euclid_assumption "" (show e.onLine DB; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show g ≠ a; assumption)) (by euclid_assumption "" (show g.onLine AB ∨ g.sameSide d AB; assumption)) (by euclid_assumption "" (show ∠ g:a:b = ∠ a:b:d; assumption)) (by euclid_assumption "" (show ∠ a:b:d > ∠ b:a:d; assumption)) (by euclid_assumption "" (show a.onLine AG; assumption)) (by euclid_assumption "" (show g.onLine AG; assumption)) (by euclid_assumption "" (show e.onLine AG; assumption)))
  -- The two triangles d-a-e and d-c-e sharing the perpendicular DE.
  have step12_tri1 : formTriangle d a e AC AG DB := by euclid_apply (helper_3_25_step12_tri1 a b c d e AC AG DB (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show ¬ b.onLine AC; assumption)) (by euclid_assumption "" (show between a d c; assumption)) (by euclid_assumption "" (show b.onLine DB; assumption)) (by euclid_assumption "" (show d.onLine DB; assumption)) (by euclid_assumption "" (show e.onLine DB; assumption)) (by euclid_assumption "" (show a.onLine AG; assumption)) (by euclid_assumption "" (show e.onLine AG; assumption)) (by euclid_assumption "" (show ¬ e.onLine AC; assumption)))
  have step12_tri2 : formTriangle d c e AC EC DB := by euclid_apply (helper_3_25_step12_tri2 a b c d e AC EC DB (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show ¬ b.onLine AC; assumption)) (by euclid_assumption "" (show between a d c; assumption)) (by euclid_assumption "" (show b.onLine DB; assumption)) (by euclid_assumption "" (show d.onLine DB; assumption)) (by euclid_assumption "" (show e.onLine DB; assumption)) (by euclid_assumption "" (show c.onLine EC; assumption)) (by euclid_assumption "" (show e.onLine EC; assumption)) (by euclid_assumption "" (show ¬ e.onLine AC; assumption)))
  -- SAS [I.4]: DA=DC, DE common, ∠ADE=∠CDE ⟹ AE=CE.
  euclid_apply (proposition_4 d a e d c e AC AG DB AC EC DB)
  euclid_finish

end Elements.Book3

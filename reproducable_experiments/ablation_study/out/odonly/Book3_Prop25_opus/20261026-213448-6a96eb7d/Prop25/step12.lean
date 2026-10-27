import SystemE
import Book1.Prop04.Main
import Book3.Prop25.step12_tri1
import Book3.Prop25.step12_tri2
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_step12 (a b c d e g : Point) (AC DB AB AG EC : Line)
    (haAC : a.onLine AC) (hcAC : c.onLine AC) (hac : a ≠ c) (hbAC : ¬b.onLine AC)
    (hbet : between a d c)
    (hdDB : d.onLine DB) (hbDB : b.onLine DB) (heDB : e.onLine DB)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hperp : ∠ a:d:b = ∟) (hgt : ∠ a:b:d > ∠ b:a:d)
    (hga : g ≠ a) (hab_ne : a ≠ b) (hg_side : g.onLine AB ∨ g.sameSide d AB)
    (hgab : ∠ g:a:b = ∠ a:b:d)
    (haAG : a.onLine AG) (hgAG : g.onLine AG) (heAG : e.onLine AG)
    (hcEC : c.onLine EC) (heEC : e.onLine EC)
    (hstep6 : ∠ b:a:e = ∠ a:b:d ∧ e ≠ a)
    (hstep10 : |(a─d)| = |(c─d)| ∧ |(d─e)| = |(d─e)|)
    (hstep11 : ∠ a:d:e = ∠ c:d:e) :
    |(a─e)| = |(c─e)| := by
  have step12_tri1 : formTriangle d a e AC AG DB := by euclid_apply (helper_3_25_step12_tri1 a b c d e g AC DB AB AG (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show ¬b.onLine AC; assumption)) (by euclid_assumption "" (show between a d c; assumption)) (by euclid_assumption "" (show d.onLine DB; assumption)) (by euclid_assumption "" (show b.onLine DB; assumption)) (by euclid_assumption "" (show e.onLine DB; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show ∠ a:d:b = ∟; assumption)) (by euclid_assumption "" (show ∠ a:b:d > ∠ b:a:d; assumption)) (by euclid_assumption "" (show g ≠ a; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show g.onLine AB ∨ g.sameSide d AB; assumption)) (by euclid_assumption "" (show ∠ g:a:b = ∠ a:b:d; assumption)) (by euclid_assumption "" (show a.onLine AG; assumption)) (by euclid_assumption "" (show g.onLine AG; assumption)) (by euclid_assumption "" (show e.onLine AG; assumption)) (by euclid_assumption "" (show ∠ b:a:e = ∠ a:b:d ∧ e ≠ a; assumption)))
  have step12_tri2 : formTriangle d c e AC EC DB := by euclid_apply (helper_3_25_step12_tri2 a b c d e g AC DB AB AG EC (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show ¬b.onLine AC; assumption)) (by euclid_assumption "" (show between a d c; assumption)) (by euclid_assumption "" (show d.onLine DB; assumption)) (by euclid_assumption "" (show b.onLine DB; assumption)) (by euclid_assumption "" (show e.onLine DB; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show ∠ a:d:b = ∟; assumption)) (by euclid_assumption "" (show ∠ a:b:d > ∠ b:a:d; assumption)) (by euclid_assumption "" (show g ≠ a; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show g.onLine AB ∨ g.sameSide d AB; assumption)) (by euclid_assumption "" (show ∠ g:a:b = ∠ a:b:d; assumption)) (by euclid_assumption "" (show a.onLine AG; assumption)) (by euclid_assumption "" (show g.onLine AG; assumption)) (by euclid_assumption "" (show e.onLine AG; assumption)) (by euclid_assumption "" (show c.onLine EC; assumption)) (by euclid_assumption "" (show e.onLine EC; assumption)) (by euclid_assumption "" (show ∠ b:a:e = ∠ a:b:d ∧ e ≠ a; assumption)))
  euclid_apply (Elements.Book1.proposition_4 d a e d c e AC AG DB AC EC DB)
  euclid_finish

end Elements.Book3

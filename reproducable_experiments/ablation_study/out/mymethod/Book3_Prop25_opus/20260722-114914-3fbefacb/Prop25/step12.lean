import SystemE
import Book1.Prop04.Main
import Book3.Prop25.step12_tri1
import Book3.Prop25.step12_tri2
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1

theorem helper_3_25_step12 (a b c d e : Point) (AC AG DB EC : Line)
    (haAC : a.onLine AC) (hcAC : c.onLine AC) (hac : a ≠ c) (hboff : ¬b.onLine AC)
    (hadc : between a d c)
    (haAG : a.onLine AG) (heAG : e.onLine AG)
    (hcEC : c.onLine EC) (heEC : e.onLine EC)
    (hdDB : d.onLine DB) (hbDB : b.onLine DB) (heDB : e.onLine DB)
    (hadbperp : ∠ a:d:b = ∟)
    (hperp2 : ∠ a:d:e = ∟ ∧ ∠ c:d:e = ∟)
    (hstep6 : ∠ b:a:e = ∠ a:b:d ∧ e ≠ a)
    (hgt : ∠ a:b:d > ∠ b:a:d)
    (hstep10 : |(a─d)| = |(c─d)| ∧ |(d─e)| = |(d─e)|)
    (h11 : ∠ a:d:e = ∠ c:d:e) :
    |(a─e)| = |(c─e)| := by
  obtain ⟨h10, _⟩ := hstep10
  obtain ⟨hbae, _⟩ := hstep6
  have step12_tri1 : formTriangle d a e AC AG DB := by euclid_apply (helper_3_25_step12_tri1 a b c d e AC AG DB (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a ≠ c; assumption)) (by euclid_assumption "" (show ¬b.onLine AC; assumption)) (by euclid_assumption "" (show between a d c; assumption)) (by euclid_assumption "" (show a.onLine AG; assumption)) (by euclid_assumption "" (show e.onLine AG; assumption)) (by euclid_assumption "" (show d.onLine DB; assumption)) (by euclid_assumption "" (show b.onLine DB; assumption)) (by euclid_assumption "" (show e.onLine DB; assumption)) (by euclid_assumption "" (show ∠ a:d:b = ∟; assumption)) (by euclid_assumption "" (show ∠ a:d:e = ∟ ∧ ∠ c:d:e = ∟; assumption)) (by euclid_assumption "" (show ∠ b:a:e = ∠ a:b:d; assumption)) (by euclid_assumption "" (show ∠ a:b:d > ∠ b:a:d; assumption)))
  have step12_tri2 : formTriangle d c e AC EC DB := by euclid_apply (helper_3_25_step12_tri2 a b c d e AC EC DB (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a ≠ c; assumption)) (by euclid_assumption "" (show ¬b.onLine AC; assumption)) (by euclid_assumption "" (show between a d c; assumption)) (by euclid_assumption "" (show c.onLine EC; assumption)) (by euclid_assumption "" (show e.onLine EC; assumption)) (by euclid_assumption "" (show d.onLine DB; assumption)) (by euclid_assumption "" (show b.onLine DB; assumption)) (by euclid_assumption "" (show e.onLine DB; assumption)) (by euclid_assumption "" (show ∠ a:d:b = ∟; assumption)) (by euclid_assumption "" (show ∠ a:d:e = ∟ ∧ ∠ c:d:e = ∟; assumption)) (by euclid_assumption "" (show ∠ b:a:e = ∠ a:b:d; assumption)) (by euclid_assumption "" (show ∠ a:b:d > ∠ b:a:d; assumption)))
  euclid_apply (proposition_4 d a e d c e AC AG DB AC EC DB)
  euclid_finish

end Elements.Book3

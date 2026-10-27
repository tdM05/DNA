import SystemE
import Book1.Prop04.Main
import Book3.Prop25.step12_tri1
import Book3.Prop25.step12_tri2
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1

theorem helper_3_25_step12 (a b c d e : Point) (AC DB EC : Line)
    (hAC_a : a.onLine AC) (hAC_c : c.onLine AC)
    (hbet : between a d c)
    (hd_DB : d.onLine DB) (he_DB : e.onLine DB)
    (hc_EC : c.onLine EC) (he_EC : e.onLine EC)
    (hright : ∠ a:d:e = ∟ ∧ ∠ c:d:e = ∟)
    (hstep6 : ∠ b:a:e = ∠ a:b:d ∧ e ≠ a)
    (hgt : ∠ a:b:d > ∠ b:a:d)
    (hstep10 : |(a─d)| = |(c─d)| ∧ |(d─e)| = |(d─e)|)
    (hstep11 : ∠ a:d:e = ∠ c:d:e) :
    |(a─e)| = |(c─e)| := by
  -- e ≠ d: were e = d, step6 would give ∠BAD = ∠ABD, contradicting ∠ABD > ∠BAD.
  have hed : e ≠ d := by euclid_finish
  -- SAS on triangles ADE, CDE: AD = CD, DE common, ∠ADE = ∠CDE ⟹ AE = CE [Prop.~1.4].
  euclid_apply (line_from_points a e) as AE
  have step12_tri1 : formTriangle d a e AC AE DB := by euclid_apply (helper_3_25_step12_tri1 a c d e AC AE DB (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show between a d c; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e.onLine AE; assumption)) (by euclid_assumption "" (show d.onLine DB; assumption)) (by euclid_assumption "" (show e.onLine DB; assumption)) (by euclid_assumption "" (show ∠ a:d:e = ∟; assumption)) (by euclid_assumption "" (show e ≠ d; assumption)))
  have step12_tri2 : formTriangle d c e AC EC DB := by euclid_apply (helper_3_25_step12_tri2 a c d e AC EC DB (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show between a d c; assumption)) (by euclid_assumption "" (show c.onLine EC; assumption)) (by euclid_assumption "" (show e.onLine EC; assumption)) (by euclid_assumption "" (show d.onLine DB; assumption)) (by euclid_assumption "" (show e.onLine DB; assumption)) (by euclid_assumption "" (show ∠ c:d:e = ∟; assumption)) (by euclid_assumption "" (show e ≠ d; assumption)))
  euclid_apply (proposition_4 d a e d c e AC AE DB AC EC DB)
  euclid_finish

end Elements.Book3

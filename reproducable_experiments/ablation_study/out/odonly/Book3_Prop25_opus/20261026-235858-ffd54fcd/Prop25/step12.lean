import SystemE
import Book1.Prop04.Main
import Book3.Prop25.step12_eoff
import Book3.Prop25.step12_t1
import Book3.Prop25.step12_t2
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_step12 (a b c d g e : Point) (AC AG DB EC AB : Line)
    (ha_AC : a.onLine AC) (hc_AC : c.onLine AC) (hadc : between a d c)
    (hb_off : ¬b.onLine AC) (hb_DB : b.onLine DB)
    (ha_AB : a.onLine AB) (hb_AB : b.onLine AB)
    (ha_AG : a.onLine AG) (hg_AG : g.onLine AG) (he_AG : e.onLine AG)
    (hga : g ≠ a) (hgab : ∠ g:a:b = ∠ a:b:d) (hgt : ∠ a:b:d > ∠ b:a:d)
    (hd_DB : d.onLine DB) (he_DB : e.onLine DB)
    (hc_EC : c.onLine EC) (he_EC : e.onLine EC)
    (hstep6 : ∠ b:a:e = ∠ a:b:d ∧ e ≠ a) (hec : e ≠ c)
    (hstep10 : |(a─d)| = |(c─d)| ∧ |(d─e)| = |(d─e)|)
    (hstep11 : ∠ a:d:e = ∠ c:d:e) :
    |(a─e)| = |(c─e)| := by
  obtain ⟨hstep6a, hea⟩ := hstep6
  have step12_eoff : ¬ e.onLine AC := by euclid_apply (helper_3_25_step12_eoff a b c d e AC DB AB (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show between a d c; assumption)) (by euclid_assumption "" (show ¬b.onLine AC; assumption)) (by euclid_assumption "" (show b.onLine DB; assumption)) (by euclid_assumption "" (show d.onLine DB; assumption)) (by euclid_assumption "" (show e.onLine DB; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show ∠ b:a:e = ∠ a:b:d; assumption)) (by euclid_assumption "" (show ∠ a:b:d > ∠ b:a:d; assumption)))
  have step12_t1 : formTriangle d a e AC AG DB := by euclid_apply (helper_3_25_step12_t1 a b c d e AC AG DB (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show between a d c; assumption)) (by euclid_assumption "" (show ¬b.onLine AC; assumption)) (by euclid_assumption "" (show b.onLine DB; assumption)) (by euclid_assumption "" (show d.onLine DB; assumption)) (by euclid_assumption "" (show e.onLine DB; assumption)) (by euclid_assumption "" (show a.onLine AG; assumption)) (by euclid_assumption "" (show e.onLine AG; assumption)) (by euclid_assumption "" (show ¬ e.onLine AC; assumption)))
  have step12_t2 : formTriangle d c e AC EC DB := by euclid_apply (helper_3_25_step12_t2 a b c d e AC EC DB (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show between a d c; assumption)) (by euclid_assumption "" (show ¬b.onLine AC; assumption)) (by euclid_assumption "" (show b.onLine DB; assumption)) (by euclid_assumption "" (show d.onLine DB; assumption)) (by euclid_assumption "" (show e.onLine DB; assumption)) (by euclid_assumption "" (show c.onLine EC; assumption)) (by euclid_assumption "" (show e.onLine EC; assumption)) (by euclid_assumption "" (show ¬ e.onLine AC; assumption)))
  -- SAS on triangles ADE, CDE: AD=CD, DE common, ∠ADE=∠CDE ⟹ AE=CE [Prop.~1.4]
  euclid_apply (Elements.Book1.proposition_4 d a e d c e AC AG DB AC EC DB)
  euclid_finish

end Elements.Book3

import SystemE
import Book1.Prop04.Main
import Book3.Prop25.hEc_eoffac
import Book3.Prop25.hEc_tri1
import Book3.Prop25.hEc_tri2
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1

theorem helper_3_25_hEc (a b c d e : Point) (AC DB AG3 : Line)
    (haAC : a.onLine AC) (hcAC : c.onLine AC) (hboff : ¬ b.onLine AC)
    (hbtw : between a d c) (hmid : |(a─d)| = |(d─c)|) (hadb : ∠ a:d:b = ∟)
    (hdDB : d.onLine DB) (hbDB : b.onLine DB) (heDB : e.onLine DB)
    (haAG3 : a.onLine AG3) (heAG3 : e.onLine AG3)
    (hbse : b.sameSide e AC) :
    |(e─a)| = |(e─c)| := by
  -- e is off AC: b and e are on the SAME side of AC (step23), so neither is on it.
  have hEc_eoffac : ¬ e.onLine AC := by euclid_apply (helper_3_25_hEc_eoffac b e AC (by euclid_assumption "" (show b.sameSide e AC; assumption)))
  have hec : e ≠ c := by euclid_finish
  euclid_apply (line_from_points e c) as EC
  -- The two triangles d-a-e and d-c-e sharing the perpendicular DE.
  have hEc_tri1 : formTriangle d a e AC AG3 DB := by euclid_apply (helper_3_25_hEc_tri1 a b c d e AC AG3 DB (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show ¬ b.onLine AC; assumption)) (by euclid_assumption "" (show between a d c; assumption)) (by euclid_assumption "" (show b.onLine DB; assumption)) (by euclid_assumption "" (show d.onLine DB; assumption)) (by euclid_assumption "" (show e.onLine DB; assumption)) (by euclid_assumption "" (show a.onLine AG3; assumption)) (by euclid_assumption "" (show e.onLine AG3; assumption)) (by euclid_assumption "" (show ¬ e.onLine AC; assumption)))
  have hEc_tri2 : formTriangle d c e AC EC DB := by euclid_apply (helper_3_25_hEc_tri2 a b c d e AC EC DB (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show ¬ b.onLine AC; assumption)) (by euclid_assumption "" (show between a d c; assumption)) (by euclid_assumption "" (show b.onLine DB; assumption)) (by euclid_assumption "" (show d.onLine DB; assumption)) (by euclid_assumption "" (show e.onLine DB; assumption)) (by euclid_assumption "" (show c.onLine EC; assumption)) (by euclid_assumption "" (show e.onLine EC; assumption)) (by euclid_assumption "" (show ¬ e.onLine AC; assumption)))
  -- Both ∠ADE and ∠CDE are right angles (DB ⊥ AC at d, e on DB).
  have hrt : ∠ a:d:e = ∟ ∧ ∠ c:d:e = ∟ := by euclid_finish
  -- SAS [I.4]: DA=DC, DE common, ∠ADE=∠CDE ⟹ AE=CE.
  euclid_apply (proposition_4 d a e d c e AC AG3 DB AC EC DB)
  euclid_finish

end Elements.Book3

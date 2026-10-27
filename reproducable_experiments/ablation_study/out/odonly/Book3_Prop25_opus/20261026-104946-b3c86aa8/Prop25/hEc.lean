import SystemE
import Book1.Prop04.Main
import Book3.Prop25.step12_tri1
import Book3.Prop25.step12_tri2
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1

theorem helper_3_25_hEc (a b c d e : Point) (AC DB : Line)
    (hAC_a : a.onLine AC) (hAC_c : c.onLine AC) (hac : a ≠ c)
    (hb_off : ¬b.onLine AC)
    (hbet : between a d c)
    (hd_DB : d.onLine DB) (hb_DB : b.onLine DB) (he_DB : e.onLine DB)
    (hadb : ∠ a:d:b = ∟)
    (hstep22 : e.onLine DB ∧ e.sameSide b AC)
    (hmid : |(a─d)| = |(d─c)|) :
    |(e─a)| = |(e─c)| := by
  -- e lies on the perpendicular bisector DB of AC: SAS on △ADE, △CDE ⟹ EA = EC.
  have hed : e ≠ d := by euclid_finish
  have hade : ∠ a:d:e = ∟ := by euclid_finish
  have hcde : ∠ c:d:e = ∟ := by euclid_finish
  euclid_apply (line_from_points a e) as AE
  euclid_apply (line_from_points c e) as EC
  have step12_tri1 : formTriangle d a e AC AE DB := by euclid_apply (helper_3_25_step12_tri1 a c d e AC AE DB (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show between a d c; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e.onLine AE; assumption)) (by euclid_assumption "" (show d.onLine DB; assumption)) (by euclid_assumption "" (show e.onLine DB; assumption)) (by euclid_assumption "" (show ∠ a:d:e = ∟; assumption)) (by euclid_assumption "" (show e ≠ d; assumption)))
  have step12_tri2 : formTriangle d c e AC EC DB := by euclid_apply (helper_3_25_step12_tri2 a c d e AC EC DB (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show between a d c; assumption)) (by euclid_assumption "" (show c.onLine EC; assumption)) (by euclid_assumption "" (show e.onLine EC; assumption)) (by euclid_assumption "" (show d.onLine DB; assumption)) (by euclid_assumption "" (show e.onLine DB; assumption)) (by euclid_assumption "" (show ∠ c:d:e = ∟; assumption)) (by euclid_assumption "" (show e ≠ d; assumption)))
  euclid_apply (proposition_4 d a e d c e AC AE DB AC EC DB)
  euclid_finish

end Elements.Book3

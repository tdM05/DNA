import SystemE
import Book1.Prop06.Main
import Book3.Prop25.hEb_bae
import Book3.Prop25.hEb_abe
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1

theorem helper_3_25_hEb (a b c d e g3 : Point) (AC DB AB AG3 : Line)
    (hAC_a : a.onLine AC) (hAC_c : c.onLine AC) (hac : a ≠ c)
    (hb_off : ¬b.onLine AC)
    (hbet : between a d c)
    (hd_DB : d.onLine DB) (hb_DB : b.onLine DB) (he_DB : e.onLine DB)
    (hAB_a : a.onLine AB) (hAB_b : b.onLine AB)
    (hadb : ∠ a:d:b = ∟)
    (hgNa : g3 ≠ a)
    (hg_side : g3.onLine AB ∨ g3.sameSide d AB)
    (hgab : ∠ g3:a:b = ∠ a:b:d)
    (hAG_a : a.onLine AG3) (hAG_g : g3.onLine AG3) (he_AG : e.onLine AG3)
    (hstep22 : e.onLine DB ∧ e.sameSide b AC)
    (hlt : ∠ a:b:d < ∠ b:a:d) :
    |(e─a)| = |(e─b)| := by
  -- Triangle ABE: ∠BAE = ∠ABE ⟹ EA = EB (isosceles converse [Prop.~1.6]).
  euclid_apply (line_from_points e a) as EA
  euclid_apply (line_from_points e b) as EB
  have hEb_bae : ∠ b:a:e = ∠ a:b:d := by euclid_apply (helper_3_25_hEb_bae a b c d e g3 AC DB AB AG3 (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show ¬b.onLine AC; assumption)) (by euclid_assumption "" (show between a d c; assumption)) (by euclid_assumption "" (show d.onLine DB; assumption)) (by euclid_assumption "" (show b.onLine DB; assumption)) (by euclid_assumption "" (show e.onLine DB; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show ∠ a:d:b = ∟; assumption)) (by euclid_assumption "" (show g3 ≠ a; assumption)) (by euclid_assumption "" (show g3.onLine AB ∨ g3.sameSide d AB; assumption)) (by euclid_assumption "" (show ∠ g3:a:b = ∠ a:b:d; assumption)) (by euclid_assumption "" (show a.onLine AG3; assumption)) (by euclid_assumption "" (show g3.onLine AG3; assumption)) (by euclid_assumption "" (show e.onLine AG3; assumption)))
  have hEb_abe : ∠ a:b:e = ∠ a:b:d := by euclid_apply (helper_3_25_hEb_abe a b c d e g3 AC DB AB AG3 (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a ≠ c; assumption)) (by euclid_assumption "" (show ¬b.onLine AC; assumption)) (by euclid_assumption "" (show between a d c; assumption)) (by euclid_assumption "" (show d.onLine DB; assumption)) (by euclid_assumption "" (show b.onLine DB; assumption)) (by euclid_assumption "" (show e.onLine DB; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show ∠ a:d:b = ∟; assumption)) (by euclid_assumption "" (show g3 ≠ a; assumption)) (by euclid_assumption "" (show g3.onLine AB ∨ g3.sameSide d AB; assumption)) (by euclid_assumption "" (show ∠ g3:a:b = ∠ a:b:d; assumption)) (by euclid_assumption "" (show a.onLine AG3; assumption)) (by euclid_assumption "" (show g3.onLine AG3; assumption)) (by euclid_assumption "" (show e.onLine AG3; assumption)) (by euclid_assumption "" (show e.sameSide b AC; assumption)) (by euclid_assumption "" (show ∠ a:b:d < ∠ b:a:d; assumption)))
  euclid_apply (proposition_6 e a b EA AB EB)
  euclid_finish

end Elements.Book3

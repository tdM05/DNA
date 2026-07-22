import SystemE
import Book1.Prop06.Main
import Book3.Prop25.hEb_bae
import Book3.Prop25.hEb_abe
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1

theorem helper_3_25_hEb (a b c d e g3 : Point) (AC DB AB AG3 : Line)
    (haAC : a.onLine AC) (hcAC : c.onLine AC) (hac : a ≠ c) (hboff : ¬b.onLine AC)
    (hadc : between a d c)
    (hdDB : d.onLine DB) (hbDB : b.onLine DB) (heDB : e.onLine DB)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hab : a ≠ b)
    (hadbperp : ∠ a:d:b = ∟)
    (hg3a : g3 ≠ a) (hg3side : g3.onLine AB ∨ g3.sameSide d AB)
    (hg3ab : ∠ g3:a:b = ∠ a:b:d)
    (haAG3 : a.onLine AG3) (hg3AG3 : g3.onLine AG3) (heAG3 : e.onLine AG3)
    (hlt : ∠ a:b:d < ∠ b:a:d)
    (step22 : e.onLine DB ∧ e.sameSide b AC) (step23 : b.sameSide e AC) :
    |(e─a)| = |(e─b)| := by
  have hEb_bae : ∠ b:a:e = ∠ a:b:d := by euclid_apply (helper_3_25_hEb_bae a b c d e g3 AC DB AB AG3 (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a ≠ c; assumption)) (by euclid_assumption "" (show ¬b.onLine AC; assumption)) (by euclid_assumption "" (show between a d c; assumption)) (by euclid_assumption "" (show d.onLine DB; assumption)) (by euclid_assumption "" (show b.onLine DB; assumption)) (by euclid_assumption "" (show e.onLine DB; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show ∠ a:d:b = ∟; assumption)) (by euclid_assumption "" (show g3 ≠ a; assumption)) (by euclid_assumption "" (show g3.onLine AB ∨ g3.sameSide d AB; assumption)) (by euclid_assumption "" (show ∠ g3:a:b = ∠ a:b:d; assumption)) (by euclid_assumption "" (show a.onLine AG3; assumption)) (by euclid_assumption "" (show g3.onLine AG3; assumption)) (by euclid_assumption "" (show e.onLine AG3; assumption)) (by euclid_assumption "" (show ∠ a:b:d < ∠ b:a:d; assumption)) (by euclid_assumption "" (show e.onLine DB ∧ e.sameSide b AC; assumption)) (by euclid_assumption "" (show b.sameSide e AC; assumption)))
  have hEb_abe : ∠ a:b:e = ∠ a:b:d := by euclid_apply (helper_3_25_hEb_abe a b c d e g3 AC DB AB AG3 (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a ≠ c; assumption)) (by euclid_assumption "" (show ¬b.onLine AC; assumption)) (by euclid_assumption "" (show between a d c; assumption)) (by euclid_assumption "" (show d.onLine DB; assumption)) (by euclid_assumption "" (show b.onLine DB; assumption)) (by euclid_assumption "" (show e.onLine DB; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show ∠ a:d:b = ∟; assumption)) (by euclid_assumption "" (show g3 ≠ a; assumption)) (by euclid_assumption "" (show g3.onLine AB ∨ g3.sameSide d AB; assumption)) (by euclid_assumption "" (show ∠ g3:a:b = ∠ a:b:d; assumption)) (by euclid_assumption "" (show a.onLine AG3; assumption)) (by euclid_assumption "" (show g3.onLine AG3; assumption)) (by euclid_assumption "" (show e.onLine AG3; assumption)) (by euclid_assumption "" (show ∠ a:b:d < ∠ b:a:d; assumption)) (by euclid_assumption "" (show e.onLine DB ∧ e.sameSide b AC; assumption)) (by euclid_assumption "" (show b.sameSide e AC; assumption)))
  -- isoceles △eab: both base angles equal ∠ a:b:d, so |e─a| = |e─b|  [Prop.~1.6]
  euclid_apply (proposition_6 e a b AG3 AB DB)
  euclid_finish

end Elements.Book3

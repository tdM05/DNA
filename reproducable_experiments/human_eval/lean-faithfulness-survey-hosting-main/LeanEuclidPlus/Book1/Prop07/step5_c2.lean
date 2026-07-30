import SystemE
import Book1Variants.Prop05
import Mathlib.Tactic.Linarith
import Book1.Prop07.step5_c2_iso
import Book1.Prop07.step5_c2_sumc
import Book1.Prop07.step5_c2_sum
import Book1.Prop07.step5_c2_s5
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_7_s5_x2 (a b c d : Point) (AB AC CB AD DB CD : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hab : a ≠ b)
    (haAC : a.onLine AC) (hcAC : c.onLine AC) (hac : a ≠ c)
    (hcCB : c.onLine CB) (hbCB : b.onLine CB) (hcb : c ≠ b)
    (haAD : a.onLine AD) (hdAD : d.onLine AD) (had : a ≠ d)
    (hdDB : d.onLine DB) (hbDB : b.onLine DB) (hdb : d ≠ b)
    (hsameSide : c.sameSide d AB) (hcd : c ≠ d)
    (hcCD : c.onLine CD) (hdCD : d.onLine CD)
    (hlen : |(a─c)| = |(a─d)|) (hlen2 : |(c─b)| = |(d─b)|)
    (s4 : ∠ a:c:d = ∠ a:d:c)
    (h1 : a.sameSide b CD) (h2 : ¬d.sameSide b AC)
    : ∠ a:d:c > ∠ d:c:b := by
  exfalso
  have s5_x6 : ∠ b:d:c = ∠ b:c:d := by euclid_apply (h_1_7_s5_x3 a b c d AB AC CB AD DB CD (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show a.onLine AC; assumption)) (by (show c.onLine AC; assumption)) (by (show a ≠ c; assumption)) (by (show c.onLine CB; assumption)) (by (show b.onLine CB; assumption)) (by (show c ≠ b; assumption)) (by (show a.onLine AD; assumption)) (by (show d.onLine AD; assumption)) (by (show a ≠ d; assumption)) (by (show d.onLine DB; assumption)) (by (show b.onLine DB; assumption)) (by (show d ≠ b; assumption)) (by (show c.sameSide d AB; assumption)) (by (show c ≠ d; assumption)) (by (show c.onLine CD; assumption)) (by (show d.onLine CD; assumption)) (by (show |(a─c)| = |(a─d)|; assumption)) (by (show |(c─b)| = |(d─b)|; assumption)) (by (show ∠ a:c:d = ∠ a:d:c; assumption)) (by (show a.sameSide b CD; assumption)) (by (show ¬d.sameSide b AC; assumption)))
  have s5_x9 : ∠ d:c:b = ∠ d:c:a + ∠ a:c:b := by euclid_apply (h_1_7_s5_x6 a b c d AB AC CB AD DB CD (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show a.onLine AC; assumption)) (by (show c.onLine AC; assumption)) (by (show a ≠ c; assumption)) (by (show c.onLine CB; assumption)) (by (show b.onLine CB; assumption)) (by (show c ≠ b; assumption)) (by (show a.onLine AD; assumption)) (by (show d.onLine AD; assumption)) (by (show a ≠ d; assumption)) (by (show d.onLine DB; assumption)) (by (show b.onLine DB; assumption)) (by (show d ≠ b; assumption)) (by (show c.sameSide d AB; assumption)) (by (show c ≠ d; assumption)) (by (show c.onLine CD; assumption)) (by (show d.onLine CD; assumption)) (by (show |(a─c)| = |(a─d)|; assumption)) (by (show |(c─b)| = |(d─b)|; assumption)) (by (show ∠ a:c:d = ∠ a:d:c; assumption)) (by (show a.sameSide b CD; assumption)) (by (show ¬d.sameSide b AC; assumption)))
  have s5_x8 : ∠ a:d:c = ∠ a:d:b + ∠ b:d:c := by euclid_apply (h_1_7_s5_x5 a b c d AB AC CB AD DB CD (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show a.onLine AC; assumption)) (by (show c.onLine AC; assumption)) (by (show a ≠ c; assumption)) (by (show c.onLine CB; assumption)) (by (show b.onLine CB; assumption)) (by (show c ≠ b; assumption)) (by (show a.onLine AD; assumption)) (by (show d.onLine AD; assumption)) (by (show a ≠ d; assumption)) (by (show d.onLine DB; assumption)) (by (show b.onLine DB; assumption)) (by (show d ≠ b; assumption)) (by (show c.sameSide d AB; assumption)) (by (show c ≠ d; assumption)) (by (show c.onLine CD; assumption)) (by (show d.onLine CD; assumption)) (by (show |(a─c)| = |(a─d)|; assumption)) (by (show |(c─b)| = |(d─b)|; assumption)) (by (show ∠ a:c:d = ∠ a:d:c; assumption)) (by (show a.sameSide b CD; assumption)) (by (show ¬d.sameSide b AC; assumption)))
  have s5_x7 : ∠ d:c:b = ∠ a:d:c + ∠ a:c:b := by euclid_apply (h_1_7_s5_x4 a b c d AC CB AD CD (by (show a.onLine AC; assumption)) (by (show c.onLine AC; assumption)) (by (show a ≠ c; assumption)) (by (show c.onLine CB; assumption)) (by (show b.onLine CB; assumption)) (by (show c ≠ b; assumption)) (by (show a.onLine AD; assumption)) (by (show d.onLine AD; assumption)) (by (show a ≠ d; assumption)) (by (show c.onLine CD; assumption)) (by (show d.onLine CD; assumption)) (by (show c ≠ d; assumption)) (by (show ∠ a:c:d = ∠ a:d:c; assumption)) (by (show ∠ d:c:b = ∠ d:c:a + ∠ a:c:b; assumption)))
  have h_bcd_sym : ∠ b:c:d = ∠ d:c:b := by euclid_finish
  have h_adb_nonneg : (0 : ℝ) ≤ ∠ a:d:b := by euclid_finish
  have h_acb_nonneg : (0 : ℝ) ≤ ∠ a:c:b := by euclid_finish
  have h_adb_zero : ∠ a:d:b = 0 := by linarith
  have h_b_on_AD : b.onLine AD := by euclid_finish
  have h_AB_eq_AD : AB = AD := by euclid_finish
  euclid_finish

end Elements.Book1

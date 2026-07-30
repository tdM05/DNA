import SystemE
import Book1.Prop07.step5_c1
import Book1.Prop07.step5_c2
import Book1.Prop07.step5_c3
import Book1.Prop07.step5_c4
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_7_s5 (a b c d : Point) (AB AC CB AD DB CD : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hab : a ≠ b)
    (haAC : a.onLine AC) (hcAC : c.onLine AC) (hac : a ≠ c)
    (hcCB : c.onLine CB) (hbCB : b.onLine CB) (hcb : c ≠ b)
    (haAD : a.onLine AD) (hdAD : d.onLine AD) (had : a ≠ d)
    (hdDB : d.onLine DB) (hbDB : b.onLine DB) (hdb : d ≠ b)
    (hsameSide : c.sameSide d AB)
    (hcd : c ≠ d)
    (hcCD : c.onLine CD) (hdCD : d.onLine CD)
    (hlen : |(a─c)| = |(a─d)|) (hlen2 : |(c─b)| = |(d─b)|)
    (s4 : ∠ a:c:d = ∠ a:d:c)
    : ∠ a:d:c > ∠ d:c:b := by
  by_cases h1 : a.sameSide b CD <;> by_cases h2 : d.sameSide b AC
  · have s5_x4 : ∠ a:d:c > ∠ d:c:b := by euclid_apply (h_1_7_s5_x1 a b c d AB AC CB AD DB CD (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a.onLine AC; assumption)) (by (show c.onLine AC; assumption)) (by (show a ≠ c; assumption)) (by (show c.onLine CB; assumption)) (by (show b.onLine CB; assumption)) (by (show c ≠ b; assumption)) (by (show a.onLine AD; assumption)) (by (show d.onLine AD; assumption)) (by (show a ≠ d; assumption)) (by (show d.onLine DB; assumption)) (by (show b.onLine DB; assumption)) (by (show d ≠ b; assumption)) (by (show c.sameSide d AB; assumption)) (by (show c ≠ d; assumption)) (by (show c.onLine CD; assumption)) (by (show d.onLine CD; assumption)) (by (show |(a─c)| = |(a─d)|; assumption)) (by (show |(c─b)| = |(d─b)|; assumption)) (by (show ∠ a:c:d = ∠ a:d:c; assumption)) (by (show a.sameSide b CD; assumption)) (by (show d.sameSide b AC; assumption)))
    exact s5_x4
  · have s5_x5 : ∠ a:d:c > ∠ d:c:b := by euclid_apply (h_1_7_s5_x2 a b c d AB AC CB AD DB CD (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show a.onLine AC; assumption)) (by (show c.onLine AC; assumption)) (by (show a ≠ c; assumption)) (by (show c.onLine CB; assumption)) (by (show b.onLine CB; assumption)) (by (show c ≠ b; assumption)) (by (show a.onLine AD; assumption)) (by (show d.onLine AD; assumption)) (by (show a ≠ d; assumption)) (by (show d.onLine DB; assumption)) (by (show b.onLine DB; assumption)) (by (show d ≠ b; assumption)) (by (show c.sameSide d AB; assumption)) (by (show c ≠ d; assumption)) (by (show c.onLine CD; assumption)) (by (show d.onLine CD; assumption)) (by (show |(a─c)| = |(a─d)|; assumption)) (by (show |(c─b)| = |(d─b)|; assumption)) (by (show ∠ a:c:d = ∠ a:d:c; assumption)) (by (show a.sameSide b CD; assumption)) (by (show ¬d.sameSide b AC; assumption)))
    exact s5_x5
  · have s5_x10 : ∠ a:d:c > ∠ d:c:b := by euclid_apply (h_1_7_s5_x7 a b c d AB AC CB AD DB CD (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a.onLine AC; assumption)) (by (show c.onLine AC; assumption)) (by (show a ≠ c; assumption)) (by (show c.onLine CB; assumption)) (by (show b.onLine CB; assumption)) (by (show c ≠ b; assumption)) (by (show a.onLine AD; assumption)) (by (show d.onLine AD; assumption)) (by (show a ≠ d; assumption)) (by (show d.onLine DB; assumption)) (by (show b.onLine DB; assumption)) (by (show d ≠ b; assumption)) (by (show c.sameSide d AB; assumption)) (by (show c ≠ d; assumption)) (by (show c.onLine CD; assumption)) (by (show d.onLine CD; assumption)) (by (show |(a─c)| = |(a─d)|; assumption)) (by (show |(c─b)| = |(d─b)|; assumption)) (by (show ∠ a:c:d = ∠ a:d:c; assumption)) (by (show ¬a.sameSide b CD; assumption)) (by (show d.sameSide b AC; assumption)))
    exact s5_x10
  · have s5_x11 : ∠ a:d:c > ∠ d:c:b := by euclid_apply (h_1_7_s5_x8 a b c d AB AC CB AD DB CD (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a.onLine AC; assumption)) (by (show c.onLine AC; assumption)) (by (show a ≠ c; assumption)) (by (show c.onLine CB; assumption)) (by (show b.onLine CB; assumption)) (by (show c ≠ b; assumption)) (by (show a.onLine AD; assumption)) (by (show d.onLine AD; assumption)) (by (show a ≠ d; assumption)) (by (show d.onLine DB; assumption)) (by (show b.onLine DB; assumption)) (by (show d ≠ b; assumption)) (by (show c.sameSide d AB; assumption)) (by (show c ≠ d; assumption)) (by (show c.onLine CD; assumption)) (by (show d.onLine CD; assumption)) (by (show |(a─c)| = |(a─d)|; assumption)) (by (show |(c─b)| = |(d─b)|; assumption)) (by (show ∠ a:c:d = ∠ a:d:c; assumption)) (by (show ¬a.sameSide b CD; assumption)) (by (show ¬d.sameSide b AC; assumption)))
    exact s5_x11

end Elements.Book1

import SystemE
import Book1.Prop06.Main

namespace Elements.Book3

open Elements.Book1

-- Since ∠ABE = ∠BAE, triangle EAB is isosceles, so EB = EA [Prop.~1.6]. Apex E, base A,B;
-- the equal base angles ∠EAB (=∠BAE) and ∠EBA (=∠ABE) force the two sides EA, EB from E equal.
theorem helper_3_25_step9 (a b e : Point) (AB DB AG : Line)
    (h1 : ∠ a:b:e = ∠ b:a:e)
    (h2 : a.onLine AB) (h3 : b.onLine AB)
    (h4 : e.onLine DB) (h5 : b.onLine DB)
    (h6 : a.onLine AG) (h7 : e.onLine AG)
    (h8 : e ≠ a) :
    |(e─b)| = |(e─a)| := by
  euclid_apply (proposition_6 e a b AG AB DB)
  euclid_finish

end Elements.Book3

import SystemE
import Book1.Prop06.Main

namespace Elements.Book3

open Elements.Book1

-- If ∠ABD = ∠BAD, triangle ABD is isosceles so AD = BD [Prop.~1.6]; together with AD = DC
-- (D the midpoint), the three radii DA, DB, DC are equal. Prop. I.6 (apex D, base A,B) turns the
-- equal base angles ∠DAB, ∠DBA into equal sides DA, DB.
theorem helper_3_25_step19 (a b c d : Point) (AB DB AC : Line)
    (h1 : ∠ a:b:d = ∠ b:a:d)
    (h2 : |(a─d)| = |(b─d)| ∧ |(a─d)| = |(d─c)|)
    (h3 : a.onLine AB) (h4 : b.onLine AB)
    (h5 : b.onLine DB) (h6 : d.onLine DB)
    (h7 : a.onLine AC) (h8 : c.onLine AC) (h9 : d.onLine AC)
    (h10 : ¬b.onLine AC) (h11 : between a d c) :
    |(d─a)| = |(d─b)| ∧ |(d─b)| = |(d─c)| := by
  euclid_apply (proposition_6 d a b AC AB DB)
  euclid_finish

end Elements.Book3

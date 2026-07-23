import SystemE

namespace Elements.Book3

open Elements.Book1

-- With ∠ABD < ∠BAD, the constructed angle ∠BAE (= ∠ABD) on BA makes the ray AG meet DB at the
-- center E, which lies on DB and inside segment ABC — i.e. on the same side of AC as B [Prop.~1.23].
theorem helper_3_25_step22 (a b c d e g3 : Point) (AB AG3 DB AC : Line)
    (h1 : ∠ a:b:d < ∠ b:a:d)
    (h2 : ∠ g3:a:b = ∠ a:b:d) (h3 : g3 ≠ a)
    (h4 : g3.onLine AB ∨ g3.sameSide d AB)
    (h5 : a.onLine AG3) (h6 : g3.onLine AG3) (h7 : e.onLine AG3)
    (h8 : e.onLine DB) (h9 : d.onLine DB) (h10 : b.onLine DB)
    (h11 : a.onLine AB) (h12 : b.onLine AB)
    (h13 : a.onLine AC) (h14 : c.onLine AC) (h15 : ¬b.onLine AC)
    (h16 : between a d c) (h17 : ∠ a:d:b = ∟) :
    e.onLine DB ∧ e.sameSide b AC := by
  euclid_finish

end Elements.Book3

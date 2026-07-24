import SystemE
import Book1.Prop06.Main

namespace Elements.Book3

open Elements.Book1

-- Angle ABD equals BAD, so triangle DAB is isosceles and AD equals BD [Prop.~1.6]; AD equals DC
-- from the bisection, hence DA, DB, DC are all equal.
theorem helper_3_25_step19 (a b c d : Point) (AB DB AC : Line)
    (hang : ∠ a:b:d = ∠ b:a:d)
    (had : |(a─d)| = |(b─d)| ∧ |(a─d)| = |(d─c)|)
    (hab1 : a.onLine AB) (hab2 : b.onLine AB)
    (hdb1 : d.onLine DB) (hdb2 : b.onLine DB)
    (hac1 : a.onLine AC) (hac2 : c.onLine AC) (hac3 : d.onLine AC)
    (hbet : between a d c) (hbAC : ¬b.onLine AC) (hac : a ≠ c) :
    |(d─a)| = |(d─b)| ∧ |(d─b)| = |(d─c)| := by
  euclid_apply (proposition_6 d a b AC AB DB)
  euclid_finish

end Elements.Book3

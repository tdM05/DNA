import SystemE

namespace Elements.Book3

-- The centre E lies on DB (it is the intersection of AE and DB), and since angle BAE (=ABD)
-- was constructed on the same side of AB as D, AE meets DB on the b-side of AC — inside the
-- segment ABC.  (The angle BAE, equal to ABD, is built by [Prop.~1.23], the construction in Main.)
theorem helper_3_25_step22 (a b c d e g3 : Point) (AB DB AC AG3 : Line)
    (hlt : ∠ a:b:d < ∠ b:a:d)
    (hang : ∠ g3:a:b = ∠ a:b:d) (hg3 : g3.onLine AB ∨ g3.sameSide d AB)
    (hg3a : g3 ≠ a)
    (hag1 : a.onLine AG3) (hag2 : g3.onLine AG3) (hage : e.onLine AG3)
    (hdb1 : d.onLine DB) (hdb2 : b.onLine DB) (hdbe : e.onLine DB)
    (hab1 : a.onLine AB) (hab2 : b.onLine AB)
    (hac1 : a.onLine AC) (hac2 : c.onLine AC) (hac3 : d.onLine AC)
    (hbet : between a d c) (hbAC : ¬b.onLine AC) (hac : a ≠ c)
    (hperp : ∠ a:d:b = ∟) :
    e.onLine DB ∧ e.sameSide b AC := by
  euclid_finish

end Elements.Book3

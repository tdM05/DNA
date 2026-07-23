import SystemE

namespace Elements.Book3

open Elements.Book1

-- Angle BAE equal to angle ABD, constructed on BA at A [Prop.~1.23]. Here e is the
-- intersection of AG (= the ray on which ∠GAB = ∠ABD was set up) with DB, so ∠BAE = ∠GAB = ∠ABD,
-- and e ≠ a since a lies on AC while e lies on the perpendicular DB (which meets AC only at d ≠ a).
theorem helper_3_25_step6 (a b c d e g : Point) (AB AG DB AC : Line)
    (h1 : ∠ g:a:b = ∠ a:b:d) (h2 : g ≠ a)
    (h3 : g.onLine AB ∨ g.sameSide d AB)
    (h4 : a.onLine AG) (h5 : g.onLine AG) (h6 : e.onLine AG)
    (h7 : e.onLine DB) (h8 : d.onLine DB) (h9 : b.onLine DB)
    (h10 : a.onLine AB) (h11 : b.onLine AB)
    (h12 : a.onLine AC) (h13 : c.onLine AC) (h14 : ¬b.onLine AC)
    (h15 : between a d c) (h16 : ∠ a:d:b = ∟) (h17 : ∠ a:b:d > ∠ b:a:d) :
    ∠ b:a:e = ∠ a:b:d ∧ e ≠ a := by
  euclid_finish

end Elements.Book3

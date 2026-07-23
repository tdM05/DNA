import SystemE

namespace Elements.Book3

theorem helper_3_25_step22 (a b c d e g3 : Point) (AC DB AB AG3 : Line)
    (h1 : ∠ g3:a:b = ∠ a:b:d) (h2 : g3 ≠ a) (h3 : g3.onLine AB ∨ g3.sameSide d AB)
    (h4 : a.onLine AG3) (h5 : g3.onLine AG3) (h6 : e.onLine AG3)
    (h7 : e.onLine DB) (h8 : d.onLine DB) (h9 : b.onLine DB)
    (h10 : a.onLine AB) (h11 : b.onLine AB)
    (h12 : a.onLine AC) (h13 : c.onLine AC) (h14 : ¬b.onLine AC)
    (h15 : between a d c) (h16 : ∠ a:b:d < ∠ b:a:d)
    (h17 : ∠ a:d:b = ∟) (h18 : |(a─b)| = |(c─b)|) (h19 : |(a─d)| = |(d─c)|) :
    e.onLine DB ∧ e.sameSide b AC := by
  euclid_finish

end Elements.Book3

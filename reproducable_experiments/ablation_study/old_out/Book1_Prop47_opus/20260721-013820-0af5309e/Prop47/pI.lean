import SystemE

namespace Elements.Book1

-- between b m c, where m = AL ∩ BC and AL ∥ BD ⊥ BC (m is foot of perp from a), ∠bac = ∟
theorem probe_I (a b c d m : Point) (AB BC AC BD AL : Line)
    (h1 : a.onLine AB) (h2 : b.onLine AB) (h3 : a ≠ b)
    (h4 : b.onLine BC) (h5 : c.onLine BC) (h6 : b ≠ c)
    (h7 : c.onLine AC) (h8 : a.onLine AC)
    (h9 : b.onLine BD) (h10 : d.onLine BD)
    (h11 : ∠ c:b:d = ∟) (h12 : ∠ b:a:c = ∟)
    (h13 : ¬(a.onLine BC)) (h14 : ¬(d.onLine BC)) (h15 : ¬(d.sameSide a BC))
    (h16 : a.onLine AL) (h17 : m.onLine AL) (h18 : m.onLine BC)
    (h19 : ¬(AL.intersectsLine BD)) (h20 : ¬(c.onLine BD))
    (h21 : |(b─d)| = |(b─c)|) (h22 : b ≠ m) (h23 : c ≠ m) :
    between b m c := by
  euclid_finish

end Elements.Book1

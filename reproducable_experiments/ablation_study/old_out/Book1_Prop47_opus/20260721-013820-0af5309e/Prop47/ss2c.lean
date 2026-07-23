import SystemE

namespace Elements.Book1

-- e.sameSide b AC, mirror of ss2 (square BDEC, foot m between b,c)
theorem helper_1_47_ss2c (a b c d e m : Point) (AB BC AC BD CE DE AL : Line)
    (h1 : a.onLine AB) (h2 : b.onLine AB) (h3 : a ≠ b)
    (h4 : b.onLine BC) (h5 : c.onLine BC)
    (h6 : c.onLine AC) (h7 : a.onLine AC)
    (h8 : b.onLine BD) (h9 : d.onLine BD)
    (h10 : c.onLine CE) (h11 : e.onLine CE)
    (h12 : d.onLine DE) (h13 : e.onLine DE)
    (h14 : ¬(BD.intersectsLine CE)) (h15 : ¬(DE.intersectsLine BC))
    (h16 : d.sameSide b CE)
    (h17 : ∠ b:c:e = ∟) (h18 : ∠ b:a:c = ∟)
    (h19 : ¬(e.onLine BC)) (h20 : ¬(a.onLine BC)) (h21 : ¬(d.sameSide a BC))
    (h22 : ¬(b.onLine AC)) (h23 : ¬(e.onLine AC))
    (h24 : a.onLine AL) (h25 : m.onLine AL) (h26 : m.onLine BC)
    (h27 : ¬(AL.intersectsLine CE)) (h28 : between b m c) :
    e.sameSide b AC := by
  euclid_finish

end Elements.Book1

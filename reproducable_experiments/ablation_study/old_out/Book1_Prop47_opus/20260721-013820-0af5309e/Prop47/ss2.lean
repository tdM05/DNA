import SystemE

namespace Elements.Book1

-- d.sameSide c AB, using between b m c and the square BDEC
theorem helper_1_47_ss2 (a b c d e m : Point) (AB BC AC BD CE DE AL : Line)
    (h1 : a.onLine AB) (h2 : b.onLine AB) (h3 : a ≠ b)
    (h4 : b.onLine BC) (h5 : c.onLine BC)
    (h6 : c.onLine AC) (h7 : a.onLine AC)
    (h8 : b.onLine BD) (h9 : d.onLine BD)
    (h10 : c.onLine CE) (h11 : e.onLine CE)
    (h12 : d.onLine DE) (h13 : e.onLine DE)
    (h14 : ¬(BD.intersectsLine CE)) (h15 : ¬(DE.intersectsLine BC))
    (h16 : d.sameSide b CE)
    (h17 : ∠ c:b:d = ∟) (h18 : ∠ b:a:c = ∟)
    (h19 : ¬(d.onLine BC)) (h20 : ¬(a.onLine BC)) (h21 : ¬(d.sameSide a BC))
    (h22 : ¬(c.onLine AB)) (h23 : ¬(d.onLine AB))
    (h24 : a.onLine AL) (h25 : m.onLine AL) (h26 : m.onLine BC)
    (h27 : ¬(AL.intersectsLine BD)) (h28 : between b m c) :
    d.sameSide c AB := by
  euclid_finish

end Elements.Book1

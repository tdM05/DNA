import SystemE

namespace Elements.Book1

-- a.sameSide c BD from the FULL square BDEC incidence + AL parallel
theorem probe_A (a b c d e g : Point) (AB BC AC BD CE DE AL : Line)
    (h1 : a.onLine AB) (h2 : b.onLine AB) (h3 : a ≠ b)
    (h4 : b.onLine BC) (h5 : c.onLine BC)
    (h6 : c.onLine AC) (h7 : a.onLine AC)
    (h8 : d.onLine BD) (h9 : b.onLine BD)
    (h10 : c.onLine CE) (h11 : e.onLine CE)
    (h12 : d.onLine DE) (h13 : e.onLine DE)
    (h14 : ¬(BD.intersectsLine CE)) (h15 : ¬(DE.intersectsLine BC))
    (h16 : d.sameSide b CE)
    (h17 : ∠ c:b:d = ∟) (h18 : ∠ b:a:c = ∟)
    (h19 : ¬(d.onLine BC)) (h20 : ¬(a.onLine BC)) (h21 : ¬(d.sameSide a BC))
    (h22 : a.onLine AL) (h23 : ¬(AL.intersectsLine BD))
    (h24 : between c a g) (h25 : ¬(a.onLine BD)) (h26 : ¬(c.onLine BD)) :
    a.sameSide c BD := by
  euclid_finish

end Elements.Book1

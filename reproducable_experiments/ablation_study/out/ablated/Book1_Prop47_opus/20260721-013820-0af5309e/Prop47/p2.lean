import SystemE

namespace Elements.Book1

theorem probe_s1 (a b c d g : Point) (AB BC AC BD AL : Line)
    (h1 : a.onLine AB) (h2 : b.onLine AB) (h3 : a ≠ b)
    (h4 : b.onLine BC) (h5 : c.onLine BC)
    (h6 : c.onLine AC) (h7 : a.onLine AC)
    (h8 : d.onLine BD) (h9 : b.onLine BD)
    (h10 : ∠ c:b:d = ∟) (h11 : ∠ b:a:c = ∟)
    (h12 : ¬(a.onLine BD)) (h13 : ¬(c.onLine BD))
    (h14 : a.onLine AL) (h15 : ¬(AL.intersectsLine BD))
    (h16 : between c a g) (h17 : |(b─d)| = |(b─c)|) :
    a.sameSide c BD := by
  euclid_finish
end Elements.Book1

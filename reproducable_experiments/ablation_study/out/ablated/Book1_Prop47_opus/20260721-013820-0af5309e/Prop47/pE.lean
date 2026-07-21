import SystemE

namespace Elements.Book1

theorem probe_E (a b c d f g m : Point) (AB BC AC BD BF AL : Line)
    (h1 : a.onLine AB) (h2 : b.onLine AB) (h3 : a ≠ b)
    (h4 : b.onLine BC) (h5 : c.onLine BC)
    (h6 : c.onLine AC) (h7 : a.onLine AC)
    (h8 : b.onLine BD) (h9 : d.onLine BD)
    (h10 : b.onLine BF) (h11 : f.onLine BF)
    (h12 : ∠ c:b:d = ∟) (h13 : ∠ a:b:f = ∟) (h14 : ∠ b:a:c = ∟)
    (h15 : ¬(d.onLine BC)) (h16 : ¬(a.onLine BC)) (h17 : ¬(d.sameSide a BC))
    (h18 : ¬(c.onLine AB)) (h19 : ¬(c.onLine BD)) (h20 : ¬(a.onLine BF))
    (h21 : ¬(BF.intersectsLine AC))
    (h22 : a.onLine AL) (h23 : ¬(AL.intersectsLine BD))
    (h24 : m.onLine AL) (h25 : m.onLine BC) (h26 : between b m c)
    (h27 : between c a g)
    (h28 : ∠ d:b:c + ∠ a:b:c = ∠ f:b:a + ∠ a:b:c) :
    ∠ d:b:a = ∠ f:b:c := by
  euclid_finish

end Elements.Book1

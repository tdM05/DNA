import SystemE

namespace Elements.Book1

-- Can we even prove AL.intersectsLine BC (the required hALBC)?
theorem probe_ALBC (a b c d : Point) (AB BC AC BD AL : Line)
    (h1 : a.onLine AB) (h2 : b.onLine AB) (h3 : a ≠ b)
    (h4 : b.onLine BC) (h5 : c.onLine BC) (h6 : b ≠ c)
    (h7 : c.onLine AC) (h8 : a.onLine AC)
    (h9 : b.onLine BD) (h10 : d.onLine BD)
    (h11 : ∠ c:b:d = ∟) (h12 : ∠ b:a:c = ∟)
    (h13 : ¬(a.onLine BC)) (h14 : ¬(d.onLine BC)) (h15 : ¬(d.sameSide a BC))
    (h16 : a.onLine AL) (h17 : ¬(AL.intersectsLine BD)) (h18 : ¬(a.onLine BD)) :
    AL.intersectsLine BC := by
  euclid_finish

end Elements.Book1

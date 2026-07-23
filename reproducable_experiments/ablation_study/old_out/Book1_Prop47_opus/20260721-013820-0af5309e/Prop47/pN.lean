import SystemE

namespace Elements.Book1

-- between b m c from full square + AL parallel to BD and CE (parallel order)
theorem probe_N (a b c d e m l : Point) (AB BC AC BD CE DE AL : Line)
    (h1 : b.onLine BC) (h2 : c.onLine BC) (h3 : b ≠ c)
    (h4 : b.onLine BD) (h5 : d.onLine BD)
    (h6 : c.onLine CE) (h7 : e.onLine CE)
    (h8 : d.onLine DE) (h9 : e.onLine DE)
    (h10 : ¬(BD.intersectsLine CE)) (h11 : ¬(DE.intersectsLine BC))
    (h12 : d.sameSide b CE)
    (h13 : ¬(d.onLine BC)) (h14 : ¬(a.onLine BC)) (h15 : ¬(d.sameSide a BC))
    (h16 : a.onLine AL) (h17 : m.onLine AL) (h18 : m.onLine BC)
    (h19 : l.onLine AL) (h20 : l.onLine DE)
    (h21 : ¬(AL.intersectsLine BD)) (h22 : ¬(AL.intersectsLine CE))
    (h23 : ¬(a.onLine DE)) (h24 : b ≠ m) (h25 : c ≠ m) :
    between b m c := by
  euclid_finish

end Elements.Book1

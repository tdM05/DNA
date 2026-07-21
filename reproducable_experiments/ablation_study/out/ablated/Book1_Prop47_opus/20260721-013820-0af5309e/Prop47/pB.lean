import SystemE

namespace Elements.Book1

-- a.sameSide c BD assuming a constructed foot m = AL∩BC with between b m c
theorem probe_B (a b c d m : Point) (BC BD AL : Line)
    (h1 : a.onLine AL) (h2 : m.onLine AL) (h3 : ¬(AL.intersectsLine BD))
    (h4 : m.onLine BC) (h5 : b.onLine BC) (h6 : c.onLine BC)
    (h7 : b.onLine BD) (h8 : d.onLine BD)
    (h9 : between b m c)
    (h10 : ¬(a.onLine BD)) (h11 : ¬(c.onLine BD)) (h12 : ¬(m.onLine BD)) :
    a.sameSide c BD := by
  euclid_finish

end Elements.Book1

import SystemE

namespace Elements.Book1

-- AL ∥ CE  (from AL ∥ BD, BD ∥ CE, uniqueness of parallels)
theorem probe_L (a b c d e m l : Point) (BC BD CE DE AL : Line)
    (h1 : b.onLine BD) (h2 : d.onLine BD)
    (h3 : c.onLine CE) (h4 : e.onLine CE)
    (h5 : ¬(BD.intersectsLine CE))
    (h6 : a.onLine AL) (h7 : ¬(AL.intersectsLine BD)) (h8 : ¬(a.onLine BD)) :
    ¬(AL.intersectsLine CE) := by
  euclid_finish

end Elements.Book1

import SystemE

namespace Elements.Book1

-- a.sameSide b CE, mirror of ss1 (perpendicular CE at c, foot m between b,c, AL ∥ CE)
theorem helper_1_47_ss1c (a b c e m : Point) (BC CE AL : Line)
    (h1 : a.onLine AL) (h2 : m.onLine AL) (h3 : ¬(AL.intersectsLine CE))
    (h4 : m.onLine BC) (h5 : b.onLine BC) (h6 : c.onLine BC)
    (h7 : c.onLine CE) (h8 : e.onLine CE)
    (h9 : between b m c)
    (h10 : ¬(a.onLine CE)) (h11 : ¬(b.onLine CE)) (h12 : ¬(m.onLine CE)) :
    a.sameSide b CE := by
  euclid_finish

end Elements.Book1

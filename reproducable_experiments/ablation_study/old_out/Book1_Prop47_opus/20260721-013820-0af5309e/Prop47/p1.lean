import SystemE

namespace Elements.Book1

theorem probe_m (b c d e m : Point) (BC DE AL : Line)
    (h1 : m.onLine BC) (h2 : b.onLine BC)
    (h3 : m.onLine AL)
    (h4 : d.onLine DE) (h5 : e.onLine DE)
    (h6 : ¬(DE.intersectsLine BC)) (h7 : DE ≠ BC) (h8 : b ≠ m) :
    m.sameSide b DE := by
  euclid_finish
end Elements.Book1

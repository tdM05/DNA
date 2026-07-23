import SystemE

namespace Elements.Book1

theorem p13para (a b d l m : Point) (AL BD BC DE : Line)
    (h1 : m.onLine AL) (h2 : l.onLine AL) (ha : a.onLine AL) (hab : ¬(a.onLine BD))
    (h3 : b.onLine BD) (h4 : d.onLine BD)
    (h5 : m.onLine BC) (h6 : b.onLine BC)
    (h7 : l.onLine DE) (h8 : d.onLine DE)
    (h9 : ¬(AL.intersectsLine BD)) (h10 : ¬(DE.intersectsLine BC)) (hdebc : DE ≠ BC)
    (h11 : b ≠ m) (h12 : b ≠ d) :
    formParallelogram m l b d AL BD BC DE := by
  euclid_finish

end Elements.Book1

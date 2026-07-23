import SystemE

namespace Elements.Book3

theorem helper_3_36_step15 (b c d e : Point) (ABC : Circle) (EB EC ED : Line)
    (h1 : e.isCentre ABC) (h2 : b.onCircle ABC) (h3 : c.onCircle ABC)
    (h4 : d.outsideCircle ABC)
    (h5 : e.onLine EB) (h6 : b.onLine EB)
    (h7 : e.onLine EC) (h8 : c.onLine EC)
    (h9 : e.onLine ED) (h10 : d.onLine ED) :
    distinctPointsOnLine e b EB ∧ distinctPointsOnLine e c EC ∧ distinctPointsOnLine e d ED := by
  euclid_finish

end Elements.Book3

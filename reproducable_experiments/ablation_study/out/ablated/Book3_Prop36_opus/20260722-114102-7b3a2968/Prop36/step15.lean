import SystemE

namespace Elements.Book3

theorem helper_3_36_step15 (b c d e : Point) (ABC : Circle) (EB EC ED : Line)
    (h1 : e.isCentre ABC) (h2 : b.onCircle ABC) (h3 : c.onCircle ABC)
    (h4 : ¬ d.insideCircle ABC) (h5 : ¬ d.onCircle ABC)
    (h6 : e.onLine EB) (h7 : b.onLine EB)
    (h8 : e.onLine EC) (h9 : c.onLine EC)
    (h10 : e.onLine ED) (h11 : d.onLine ED) :
    distinctPointsOnLine e b EB ∧ distinctPointsOnLine e c EC ∧ distinctPointsOnLine e d ED := by
  euclid_finish

end Elements.Book3

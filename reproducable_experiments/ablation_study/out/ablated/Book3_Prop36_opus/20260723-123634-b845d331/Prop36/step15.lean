import SystemE

namespace Elements.Book3

-- EB, EC, and ED be joined.
theorem helper_3_36_step15 (b c d e : Point) (ABC : Circle) (EB EC ED : Line)
    (h1 : e.onLine EB) (h2 : b.onLine EB)
    (h3 : e.onLine EC) (h4 : c.onLine EC)
    (h5 : e.onLine ED) (h6 : d.onLine ED)
    (h7 : e.isCentre ABC) (h8 : b.onCircle ABC) (h9 : c.onCircle ABC)
    (h10 : ¬ d.insideCircle ABC) (h11 : ¬ d.onCircle ABC) :
    distinctPointsOnLine e b EB ∧ distinctPointsOnLine e c EC ∧ distinctPointsOnLine e d ED := by
  euclid_finish

end Elements.Book3

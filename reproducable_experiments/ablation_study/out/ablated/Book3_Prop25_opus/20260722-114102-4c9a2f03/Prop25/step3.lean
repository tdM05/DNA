import SystemE

namespace Elements.Book3

theorem helper_3_25_step3 (a b : Point) (AC AB : Line)
    (h1 : a.onLine AB) (h2 : b.onLine AB) (h3 : a.onLine AC) (h4 : ¬b.onLine AC) :
    distinctPointsOnLine a b AB := by
  euclid_finish

end Elements.Book3

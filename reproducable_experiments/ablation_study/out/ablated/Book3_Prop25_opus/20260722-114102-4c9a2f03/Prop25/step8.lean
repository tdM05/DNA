import SystemE

namespace Elements.Book3

theorem helper_3_25_step8 (c e : Point) (EC : Line)
    (h1 : e.onLine EC) (h2 : c.onLine EC) (h3 : e ≠ c) :
    distinctPointsOnLine e c EC := by
  euclid_finish

end Elements.Book3

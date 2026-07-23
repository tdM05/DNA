import SystemE

namespace Elements.Book3

theorem helper_3_36_step2 (f b : Point) (ABC : Circle) (FB : Line)
    (h1 : f.isCentre ABC) (h2 : b.onCircle ABC)
    (h3 : f.onLine FB) (h4 : b.onLine FB) :
    distinctPointsOnLine f b FB := by
  euclid_finish

end Elements.Book3

import SystemE

namespace Elements.Book3

theorem helper_3_11_step2 (a f g : Point) (ABC ADE : Circle) (AF AG : Line)
    (h1 : a.onLine AF) (h2 : f.onLine AF) (h3 : a.onLine AG) (h4 : g.onLine AG)
    (h5 : a.onCircle ABC) (h6 : f.isCentre ABC) (h7 : a.onCircle ADE) (h8 : g.isCentre ADE) :
    distinctPointsOnLine a f AF ∧ distinctPointsOnLine a g AG := by
  euclid_finish

end Elements.Book3

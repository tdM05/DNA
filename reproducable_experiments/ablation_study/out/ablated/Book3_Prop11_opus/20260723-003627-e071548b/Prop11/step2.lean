import SystemE

namespace Elements.Book3

theorem helper_3_11_step2 (a f g : Point) (ABC ADE : Circle) (AF AG : Line)
    (h1 : a.onLine AF) (h2 : f.onLine AF)
    (h3 : a.onLine AG) (h4 : g.onLine AG)
    (h5 : f.isCentre ABC) (h6 : a.onCircle ABC)
    (h7 : g.isCentre ADE) (h8 : a.onCircle ADE) :
    distinctPointsOnLine a f AF ∧ distinctPointsOnLine a g AG := by
  euclid_finish

end Elements.Book3

import SystemE

namespace Elements.Book1

theorem helper_1_47_step3 (a c d f : Point) (AD FC BD : Line)
    (h1 : a.onLine AD) (h2 : d.onLine AD) (h3 : f.onLine FC) (h4 : c.onLine FC)
    (h5 : ¬(a.onLine BD)) (h6 : d.onLine BD) (h7 : f ≠ c) :
    distinctPointsOnLine a d AD ∧ distinctPointsOnLine f c FC := by
  euclid_finish

end Elements.Book1

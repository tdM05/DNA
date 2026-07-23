import SystemE

namespace Elements.Book3

theorem helper_3_36_step14 (a c e f : Point) (ABC : Circle) (DA EF : Line)
    (h1 : ¬(∃ g : Point, g.isCentre ABC ∧ g.onLine DA))
    (h2 : e.isCentre ABC)
    (h3 : f.onLine DA) (h4 : e.onLine EF) (h5 : f.onLine EF)
    (h6 : ∠ a:f:e = ∟ ∨ ∠ c:f:e = ∟) :
    f.onLine DA ∧ distinctPointsOnLine e f EF ∧ (∠ a:f:e = ∟ ∨ ∠ c:f:e = ∟) := by
  euclid_finish

end Elements.Book3

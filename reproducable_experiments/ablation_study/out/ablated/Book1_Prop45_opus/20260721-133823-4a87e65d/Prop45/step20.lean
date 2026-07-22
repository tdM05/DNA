import SystemE

namespace Elements.Book1

theorem helper_1_45_step20 (f k l m : Point) (FG KH FK LM : Line)
    (h1 : f.onLine FG) (h2 : k.onLine KH) (h3 : f.onLine FK) (h4 : k.onLine FK)
    (h5 : l.onLine LM) (h6 : m.onLine LM) (h7 : m ≠ l) (h8 : ¬(FG.intersectsLine KH))
    (h9 : |(k─f)| = |(m─l)| ∧ ¬(FK.intersectsLine LM))
    (h10 : distinctPointsOnLine k m KH ∧ distinctPointsOnLine f l FG) :
    formParallelogram f l k m FG KH FK LM := by
  euclid_finish

end Elements.Book1

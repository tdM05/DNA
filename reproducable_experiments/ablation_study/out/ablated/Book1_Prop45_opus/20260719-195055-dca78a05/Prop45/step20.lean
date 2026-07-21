import SystemE

namespace Elements.Book1

theorem helper_1_45_step20 (f g k l m : Point) (FG KH FK LM GL HM : Line)
    (h1 : f.onLine FG) (h2 : l.onLine GL) (h3 : FG = GL)
    (h4 : k.onLine KH) (h5 : m.onLine HM) (h6 : KH = HM)
    (h7 : f.onLine FK) (h8 : k.onLine FK) (h9 : m.onLine LM) (h10 : l.onLine LM) (h11 : m ≠ l)
    (h12 : |(k─f)| = |(m─l)| ∧ ¬(FK.intersectsLine LM))
    (h13 : |(k─m)| = |(f─l)| ∧ ¬(KH.intersectsLine FG)) :
    formParallelogram f l k m FG KH FK LM := by
  euclid_finish

end Elements.Book1

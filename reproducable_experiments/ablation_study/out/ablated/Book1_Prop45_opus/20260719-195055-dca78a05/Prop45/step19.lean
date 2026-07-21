import SystemE
import Book1.Prop33.Main

namespace Elements.Book1

theorem helper_1_45_step19 (f g k l m : Point) (FK LM FG KH GL : Line)
    (h1 : |(k─f)| = |(m─l)| ∧ ¬(FK.intersectsLine LM))
    (h2 : distinctPointsOnLine k m KH ∧ distinctPointsOnLine f l FG)
    (h3 : FG = GL)
    (h4 : f.onLine FK) (h5 : k.onLine FK) (h6 : l.onLine LM) (h7 : m.onLine LM) (h8 : m ≠ l)
    (h9 : f.onLine FG) (h10 : l.onLine GL) (h11 : ¬(FG.intersectsLine KH)) :
    |(k─m)| = |(f─l)| ∧ ¬(KH.intersectsLine FG) := by
  euclid_apply (proposition_33 f k l m FK LM FG KH)
  euclid_finish

end Elements.Book1

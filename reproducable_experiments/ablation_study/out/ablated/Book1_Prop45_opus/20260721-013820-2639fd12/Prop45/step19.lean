import SystemE
import Book1.Prop33.Main

namespace Elements.Book1

theorem helper_1_45_step19 (f g h k l m : Point) (FK LM KH FG HM : Line)
    (h1 : k.onLine FK) (h2 : f.onLine FK)
    (h3 : m.onLine LM) (h4 : l.onLine LM) (h5 : m ≠ l)
    (h6 : distinctPointsOnLine k m KH ∧ distinctPointsOnLine f l FG)
    (h7 : |(k─f)| = |(m─l)| ∧ ¬(FK.intersectsLine LM))
    (h8 : k.onLine KH) (h9 : m.onLine HM) (h10 : KH = HM)
    (h11 : ¬(FG.intersectsLine KH))
    (h12 : f.onLine FG) (h13 : g.onLine FG) :
    |(k─m)| = |(f─l)| ∧ ¬(KH.intersectsLine FG) := by
  euclid_apply (proposition_33 k f m l FK LM KH FG)
  euclid_finish

end Elements.Book1

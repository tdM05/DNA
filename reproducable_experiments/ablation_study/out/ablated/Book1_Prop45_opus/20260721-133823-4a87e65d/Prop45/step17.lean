import SystemE
import Book1.Prop30.Main

namespace Elements.Book1

theorem helper_1_45_step17 (f g h k l m : Point) (FK GH LM : Line)
    (h1 : |(f─k)| = |(h─g)| ∧ ¬(FK.intersectsLine GH))
    (h2 : |(h─g)| = |(m─l)| ∧ ¬(GH.intersectsLine LM))
    (h3 : f.onLine FK) (h4 : k.onLine FK) (h5 : m.onLine LM) (h6 : l.onLine LM)
    (h7 : ¬k.onLine GH) (h8 : ¬m.onLine GH) (h9 : ¬m.sameSide k GH) (h10 : f.sameSide k GH) :
    |(k─f)| = |(m─l)| ∧ ¬(FK.intersectsLine LM) := by
  euclid_apply (proposition_30 FK LM GH)
  euclid_finish

end Elements.Book1

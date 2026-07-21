import SystemE
import Book1.Prop30.Main

namespace Elements.Book1

theorem helper_1_45_step17 (f g h k l m : Point) (FK LM GH : Line)
    (h1 : |(f─k)| = |(h─g)| ∧ ¬(FK.intersectsLine GH))
    (h2 : |(h─g)| = |(m─l)| ∧ ¬(GH.intersectsLine LM))
    (h3 : k.onLine FK) (h4 : f.onLine FK)
    (h5 : m.onLine LM) (h6 : l.onLine LM)
    (h7 : f.sameSide k GH)
    (h8 : k.opposingSides m GH ∧ (∠ k:h:g + ∠ g:h:m = ∟ + ∟))
    (h9 : g.onLine GH) (h10 : h.onLine GH) :
    |(k─f)| = |(m─l)| ∧ ¬(FK.intersectsLine LM) := by
  euclid_apply (proposition_30 FK LM GH)
  euclid_finish

end Elements.Book1

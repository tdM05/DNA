import SystemE
import Book1.Prop14.Main

namespace Elements.Book1

theorem helper_1_45_step16 (f g h k l m : Point) (GH FG GL LM : Line)
    (h1 : h.onLine GH) (h2 : g.onLine GH) (h2b : g ≠ h)
    (h3 : g.onLine FG) (h4 : f.onLine FG)
    (h5 : g.onLine GL) (h6 : l.onLine GL)
    (h7 : f.sameSide k GH)
    (h8 : k.opposingSides m GH ∧ (∠ k:h:g + ∠ g:h:m = ∟ + ∟))
    (h9 : l.onLine LM) (h10 : m.onLine LM) (h11 : ¬(GH.intersectsLine LM))
    (h12 : ∠ h:g:f + ∠ h:g:l = ∟ + ∟) :
    FG = GL := by
  euclid_apply (proposition_14 h g f l GH FG GL)
  euclid_finish

end Elements.Book1

import SystemE
import Book1.Prop14.Main

namespace Elements.Book1

theorem helper_1_45_step16 (f g h k l m : Point) (GH FG GL LM : Line)
    (h1 : g.onLine GH) (h2 : h.onLine GH) (h3 : g ≠ h)
    (h4 : g.onLine FG) (h5 : f.onLine FG) (h6 : g.onLine GL) (h7 : l.onLine GL)
    (h8 : f.sameSide k GH) (h9 : ¬m.sameSide k GH) (h10 : m.onLine LM) (h11 : l.onLine LM)
    (h12 : ¬(GH.intersectsLine LM)) (h13 : ¬k.onLine GH) (h14 : ¬m.onLine GH)
    (h15 : ∠ h:g:f + ∠ h:g:l = ∟ + ∟) :
    FG = GL := by
  euclid_apply (proposition_14 h g f l GH FG GL)
  euclid_finish

end Elements.Book1

import SystemE
import Book1.Prop14.Main

namespace Elements.Book1

theorem helper_1_45_step10 (g h k m : Point) (GH KH HM : Line)
    (h1 : g.onLine GH) (h2 : h.onLine GH) (h3 : g ≠ h)
    (h4 : h.onLine KH) (h5 : k.onLine KH) (h6 : h.onLine HM) (h7 : m.onLine HM)
    (h8 : ¬k.onLine GH) (h9 : ¬m.onLine GH) (h10 : ¬m.sameSide k GH)
    (h11 : ∠ k:h:g + ∠ g:h:m = ∟ + ∟) :
    KH = HM := by
  euclid_apply (proposition_14 g h k m GH KH HM)
  euclid_finish

end Elements.Book1

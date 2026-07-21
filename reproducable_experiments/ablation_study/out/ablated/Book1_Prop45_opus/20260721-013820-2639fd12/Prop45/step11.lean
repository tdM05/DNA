import SystemE
import Book1Variants.Prop29

namespace Elements.Book1

theorem helper_1_45_step11 (f g h k m : Point) (FG HM GH KH : Line)
    (h1 : f.onLine FG) (h2 : g.onLine FG)
    (h3 : h.onLine HM) (h4 : m.onLine HM)
    (h5 : g.onLine GH) (h6 : h.onLine GH) (h6b : g ≠ h)
    (h7 : f.sameSide k GH)
    (h8 : k.opposingSides m GH ∧ (∠ k:h:g + ∠ g:h:m = ∟ + ∟))
    (h9 : KH = HM)
    (h10 : ¬(FG.intersectsLine KH)) :
    ∠ m:h:g = ∠ h:g:f := by
  euclid_apply (proposition_29''' f m g h FG HM GH)
  euclid_finish

end Elements.Book1

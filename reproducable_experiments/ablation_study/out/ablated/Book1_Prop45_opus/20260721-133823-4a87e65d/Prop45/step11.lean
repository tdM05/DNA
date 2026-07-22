import SystemE
import Book1Variants.Prop29

namespace Elements.Book1

theorem helper_1_45_step11 (f g h k m : Point) (FG GH HM KH : Line)
    (h1 : f.onLine FG) (h2 : g.onLine FG) (h3 : g.onLine GH) (h4 : h.onLine GH)
    (h5 : g ≠ h) (h6 : h.onLine HM) (h7 : m.onLine HM) (h8 : ¬m.onLine GH)
    (h9 : f.sameSide k GH) (h10 : ¬m.sameSide k GH) (h11 : KH = HM)
    (h12 : ¬(FG.intersectsLine KH)) :
    ∠ m:h:g = ∠ h:g:f := by
  euclid_apply (proposition_29''' f m g h FG HM GH)
  euclid_finish

end Elements.Book1

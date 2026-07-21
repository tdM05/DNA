import SystemE
import Book1Variants.Prop29

namespace Elements.Book1

theorem helper_1_45_step11 (f g h k m : Point) (FG KH GH HM : Line)
    (h1 : f.onLine FG) (h2 : g.onLine FG) (h3 : g.onLine GH) (h4 : h.onLine GH) (h5 : g ≠ h)
    (h6 : h.onLine KH) (h7 : m.onLine HM) (h8 : KH = HM)
    (h9 : ¬(FG.intersectsLine KH))
    (h10 : f.sameSide k GH) (h11 : ¬m.onLine GH) (h12 : ¬(m.sameSide k GH)) (h13 : ¬k.onLine GH) :
    ∠ m:h:g = ∠ h:g:f := by
  euclid_apply (proposition_29''' f m g h FG KH GH)
  euclid_finish

end Elements.Book1

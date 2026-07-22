import SystemE
import Book1Variants.Prop29

namespace Elements.Book1

theorem helper_1_45_step14 (e₁ e₂ e₃ g h l m : Point) (HM GL GH LM : Line)
    (h1 : h.onLine HM) (h2 : m.onLine HM) (h3 : g.onLine GL) (h4 : l.onLine GL)
    (h5 : h.onLine GH) (h6 : g.onLine GH) (h7 : g ≠ h) (h8 : m.onLine LM) (h9 : l.onLine LM)
    (h10 : m ≠ l) (h11 : h.sameSide g LM) (h12 : ¬(HM.intersectsLine GL)) (h13 : ¬(GH.intersectsLine LM))
    (h14 : ∠ g:h:m = ∠ e₁:e₂:e₃) (h15 : ∠ e₁:e₂:e₃ > 0) :
    ∠ m:h:g + ∠ h:g:l = ∟ + ∟ := by
  euclid_apply (proposition_29''''' m l h g HM GL GH)
  euclid_finish

end Elements.Book1

import SystemE
import Book1Variants.Prop29

namespace Elements.Book1

theorem helper_1_45_step14 (g h l m : Point) (GL HM GH LM : Line)
    (h1 : g.onLine GL) (h2 : l.onLine GL) (h3 : h.onLine HM) (h4 : m.onLine HM)
    (h5 : ¬(HM.intersectsLine GL)) (h6 : m.onLine LM) (h7 : l.onLine LM) (h8 : ¬(GH.intersectsLine LM))
    (h9 : g.onLine GH) (h10 : h.onLine GH) (h11 : g ≠ h) :
    ∠ m:h:g + ∠ h:g:l = ∟ + ∟ := by
  euclid_apply (proposition_29''''' l m g h GL HM GH)
  euclid_finish

end Elements.Book1

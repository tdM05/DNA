import SystemE
import Book1Variants.Prop29

namespace Elements.Book1

theorem helper_1_45_step14 (g h l m : Point) (GL HM GH LM : Line)
    (h1 : g.onLine GL) (h2 : l.onLine GL)
    (h3 : h.onLine HM) (h4 : m.onLine HM)
    (h5 : g.onLine GH) (h6 : h.onLine GH) (h6b : g ≠ h)
    (h7 : m.onLine LM) (h8 : l.onLine LM) (h9 : m ≠ l)
    (h10 : ¬(GH.intersectsLine LM)) (h11 : ¬(HM.intersectsLine GL)) :
    ∠ m:h:g + ∠ h:g:l = ∟ + ∟ := by
  euclid_apply (proposition_29''''' l m g h GL HM GH)
  euclid_finish

end Elements.Book1

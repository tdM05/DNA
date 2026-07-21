import SystemE
import Book1.Prop27.Main

namespace Elements.Book1

theorem helper_1_30_step7 (a c d g k : Point) (AB CD GK : Line)
    (h1 : a.onLine AB) (h2 : g.onLine AB) (h3 : g ≠ a)
    (h4 : k.onLine CD) (h5 : d.onLine CD) (h6 : between c k d)
    (h7 : g.onLine GK) (h8 : k.onLine GK) (h9 : g ≠ k)
    (h10 : a.opposingSides d GK) (h11 : ∠ a:g:k = ∠ g:k:d) :
    ¬(AB.intersectsLine CD) := by
  euclid_apply (proposition_27 a d g k AB CD GK)
  euclid_finish

end Elements.Book1

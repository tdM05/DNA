import SystemE
import Book1.Prop27.Main
import Book1.Prop29.Main

namespace Elements.Book1

theorem helper_1_30_step7 (a c d g k : Point) (AB CD GK : Line)
  (hs5 : ∠ a:g:k = ∠ g:k:d) (hs6 : a.opposingSides d GK)
  (f9 : a.onLine AB) (f1 : g.onLine AB) (f8 : g ≠ a)
  (f2 : k.onLine CD) (f18 : d.onLine CD) (f19 : between c k d)
  (f4 : g.onLine GK) (f5 : k.onLine GK) (f3 : g ≠ k)
  : ¬(AB.intersectsLine CD) := by
  euclid_apply (proposition_27 a d g k AB CD GK)

end Elements.Book1

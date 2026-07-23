import SystemE
import Book1.Prop14.Main

namespace Elements.Book1

theorem helper_1_47_step5 (a b c g : Point) (AB AC AG : Line)
    (h1 : a.onLine AB) (h2 : b.onLine AB) (h3 : a ≠ b)
    (h4 : a.onLine AC) (h5 : c.onLine AC)
    (h6 : a.onLine AG) (h7 : g.onLine AG)
    (h8 : c.opposingSides g AB ∧ (∠ b:a:c + ∠ b:a:g = ∟ + ∟)) :
    between c a g := by
  euclid_apply (proposition_14 b a c g AB AC AG)
  euclid_finish

end Elements.Book1

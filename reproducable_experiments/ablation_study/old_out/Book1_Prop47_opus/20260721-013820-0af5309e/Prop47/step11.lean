import SystemE
import Book1.Prop04.Main

namespace Elements.Book1

theorem helper_1_47_step11 (a b c d f : Point) (AB BC BD AD FC BF : Line)
    (h1 : b.onLine BD) (h2 : d.onLine BD)
    (h3 : a.onLine AD) (h4 : d.onLine AD)
    (h5 : a.onLine AB) (h6 : b.onLine AB)
    (h7 : b.onLine BC) (h8 : c.onLine BC)
    (h9 : c.onLine FC) (h10 : f.onLine FC)
    (h11 : b.onLine BF) (h12 : f.onLine BF)
    (h13 : ¬(a.onLine BD)) (h14 : a ≠ b)
    (h15 : ∠ c:b:d = ∟) (h16 : ∠ b:a:c = ∟) (h17 : ∠ a:b:f = ∟)
    (h18 : |(d─b)| = |(c─b)| ∧ |(b─a)| = |(b─f)|)
    (h19 : ∠ d:b:a = ∠ f:b:c) :
    |(a─d)| = |(f─c)| := by
  euclid_apply (proposition_4 b d a b c f BD AD AB BC FC BF)
  euclid_finish

end Elements.Book1

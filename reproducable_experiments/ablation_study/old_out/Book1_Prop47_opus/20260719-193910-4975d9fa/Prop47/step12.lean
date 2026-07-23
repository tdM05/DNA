import SystemE
import Book1.Prop04.Main

namespace Elements.Book1

theorem helper_1_47_step12 (a b c d f : Point) (BD AD AB BC FC BF : Line)
    (hbd1 : b.onLine BD) (hbd2 : d.onLine BD)
    (had1 : d.onLine AD) (had2 : a.onLine AD)
    (hab1 : a.onLine AB) (hab2 : b.onLine AB)
    (hbc1 : b.onLine BC) (hbc2 : c.onLine BC)
    (hfc1 : c.onLine FC) (hfc2 : f.onLine FC)
    (hbf1 : f.onLine BF) (hbf2 : b.onLine BF)
    (h8 : ∠ d:b:a = ∠ f:b:c)
    (h9 : |(d─b)| = |(c─b)| ∧ |(b─a)| = |(b─f)|)
    (h11 : |(a─d)| = |(f─c)|) :
    Triangle.area △ a:b:d = Triangle.area △ f:b:c := by
  euclid_apply (proposition_4 b d a b c f BD AD AB BC FC BF)
  euclid_finish

end Elements.Book1

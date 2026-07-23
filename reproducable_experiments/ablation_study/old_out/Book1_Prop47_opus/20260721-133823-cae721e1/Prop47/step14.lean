import SystemE
import Book1.Prop41.Main

namespace Elements.Book1

theorem helper_1_47_step14 (a b c f g : Point) (AG BF AB GF BC FC AC : Line)
    (h1 : a.onLine AG) (h2 : g.onLine AG)
    (h3 : b.onLine BF) (h4 : f.onLine BF)
    (h5 : a.onLine AB) (h6 : b.onLine AB)
    (h7 : g.onLine GF) (h8 : f.onLine GF)
    (h9 : b.onLine BC) (h10 : c.onLine BC)
    (h11 : f.onLine FC) (h12 : c.onLine FC)
    (h13 : ¬(AG.intersectsLine BF)) (h14 : ¬(g.onLine AB))
    (h15 : between c a g)
    (h16 : f.onLine BF ∧ b.onLine BF ∧ ¬(BF.intersectsLine AC)) :
    Triangle.area △ a:g:f + Triangle.area △ a:f:b =
      Triangle.area △ f:b:c + Triangle.area △ f:b:c := by
  euclid_apply (proposition_41 a b f g c AG BF AB GF BC FC)
  euclid_finish

end Elements.Book1

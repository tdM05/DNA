import SystemE
import Book1.Prop41.Main

namespace Elements.Book1

theorem helper_1_47_step14 (a b c f g : Point) (AC BF GF AB FC BC : Line)
    (hassum : f.onLine BF ∧ b.onLine BF ∧ ¬(BF.intersectsLine AC))
    (h1 : g.onLine GF) (h2 : f.onLine GF) (h3 : ¬(GF.intersectsLine AB))
    (h4 : a.onLine AB) (h5 : b.onLine AB) (h6 : a ≠ b)
    (h7 : a.onLine AC) (h8 : c.onLine AC)
    (h9 : between c a g)
    (h10 : c.onLine FC) (h11 : f.onLine FC)
    (h12 : b.onLine BC) (h13 : c.onLine BC)
    (h14 : ¬(c.onLine AB)) (h15 : AB ≠ BC) (h16 : BC ≠ AC) (h17 : AC ≠ AB)
    (h18 : ∠ a:b:f = ∟) (h19 : ∠ b:a:c = ∟) :
    Triangle.area △ a:g:f + Triangle.area △ a:f:b =
      Triangle.area △ f:b:c + Triangle.area △ f:b:c := by
  euclid_apply (proposition_41 g f b a c AC BF GF AB FC BC)
  euclid_apply (parallelogram_area g a f b AC BF GF AB)
  euclid_finish

end Elements.Book1

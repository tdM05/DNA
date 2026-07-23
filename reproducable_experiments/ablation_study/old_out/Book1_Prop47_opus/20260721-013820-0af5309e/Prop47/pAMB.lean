import SystemE
import Book1Variants.Prop29

namespace Elements.Book1

-- Derive AL ⊥ BC (∠ a:m:b = ∟) via extending BD and applying proposition_29'''''
theorem probe_AMB (a b c d m : Point) (AB BC AC BD AL : Line)
    (h1 : a.onLine AB) (h2 : b.onLine AB) (h3 : a ≠ b)
    (h4 : b.onLine BC) (h5 : c.onLine BC) (h6 : b ≠ c)
    (h7 : c.onLine AC) (h8 : a.onLine AC)
    (h9 : b.onLine BD) (h10 : d.onLine BD)
    (h11 : ∠ c:b:d = ∟)
    (h13 : ¬(a.onLine BC)) (h14 : ¬(d.onLine BC)) (h15 : ¬(d.sameSide a BC))
    (h16 : a.onLine AL) (h17 : m.onLine AL) (h18 : m.onLine BC)
    (h19 : ¬(AL.intersectsLine BD)) (h20 : ¬(a.onLine BD)) (h21 : a ≠ m) (h22 : b ≠ m) :
    ∠ a:m:b = ∟ := by
  euclid_apply (extend_point BD d b) as d'
  euclid_apply (proposition_29''''' a d' m b AL BD BC)
  euclid_finish

end Elements.Book1

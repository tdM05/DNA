import SystemE
import Book1Variants.Prop29

namespace Elements.Book1

-- AL ⊥ BC at the foot m: ∠ a:m:b = ∟ and ∠ a:m:c = ∟
theorem helper_1_47_amperp (a b c d m : Point) (BC BD AL : Line)
    (h4 : b.onLine BC) (h5 : c.onLine BC) (h6 : b ≠ c)
    (h9 : b.onLine BD) (h10 : d.onLine BD)
    (h11 : ∠ c:b:d = ∟)
    (h13 : ¬(a.onLine BC)) (h14 : ¬(d.onLine BC)) (h15 : ¬(d.sameSide a BC))
    (h16 : a.onLine AL) (h17 : m.onLine AL) (h18 : m.onLine BC)
    (h19 : ¬(AL.intersectsLine BD)) (h20 : ¬(a.onLine BD)) (h21 : a ≠ m)
    (h22 : b ≠ m) (h23 : c ≠ m) :
    ∠ a:m:b = ∟ ∧ ∠ a:m:c = ∟ := by
  euclid_apply (extend_point BD d b) as d'
  euclid_apply (proposition_29''''' a d' m b AL BD BC)
  euclid_finish

end Elements.Book1

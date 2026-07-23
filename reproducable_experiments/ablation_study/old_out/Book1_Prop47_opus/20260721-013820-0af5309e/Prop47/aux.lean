import SystemE
import Book1.Prop17.Main

namespace Elements.Book1

-- ¬(a.onLine BD): else ∠CBA = ∟ = ∠BAC gives a triangle with two right angles (Prop 1.17).
theorem helper_1_47_offbd (a b c d : Point) (AB BC AC BD : Line)
    (h1 : a.onLine AB) (h2 : b.onLine AB) (h3 : a ≠ b)
    (h4 : b.onLine BC) (h5 : c.onLine BC)
    (h6 : c.onLine AC) (h7 : a.onLine AC)
    (h8 : b.onLine BD) (h9 : d.onLine BD)
    (h10 : ∠ c:b:d = ∟) (h11 : ∠ b:a:c = ∟)
    (h12 : AB ≠ BC) (h13 : BC ≠ AC) (h14 : AC ≠ AB) :
    ¬(a.onLine BD) := by
  by_contra hcon
  have hcba : ∠ c:b:a = ∟ := by euclid_finish
  euclid_apply (proposition_17 c b a BC AB AC)
  euclid_finish

-- AL.intersectsLine BC  (small context)
theorem helper_1_47_albc (a b c d : Point) (AB BC AC BD AL : Line)
    (h1 : a.onLine AB) (h2 : b.onLine AB) (h3 : a ≠ b)
    (h4 : b.onLine BC) (h5 : c.onLine BC)
    (h7 : c.onLine AC) (h8 : a.onLine AC)
    (h9 : b.onLine BD) (h10 : d.onLine BD)
    (h11 : ∠ c:b:d = ∟) (h12 : ∠ b:a:c = ∟)
    (h13 : ¬(a.onLine BC)) (h14 : ¬(d.onLine BC)) (h15 : ¬(d.sameSide a BC))
    (h16 : a.onLine AL) (h17 : ¬(AL.intersectsLine BD)) (h18 : ¬(a.onLine BD)) :
    AL.intersectsLine BC := by
  euclid_finish

-- AL.intersectsLine DE  (small context; AL ∥ BD crosses DE ∥ BC)
theorem helper_1_47_alde (a b c d e : Point) (AB BC AC BD DE AL : Line)
    (h1 : a.onLine AB) (h2 : b.onLine AB) (h3 : a ≠ b)
    (h4 : b.onLine BC) (h5 : c.onLine BC)
    (h9 : b.onLine BD) (h10 : d.onLine BD)
    (h11 : ∠ c:b:d = ∟)
    (h13 : ¬(a.onLine BC)) (h14 : ¬(d.onLine BC)) (h15 : ¬(d.sameSide a BC))
    (hd : d.onLine DE) (he : e.onLine DE) (hde : ¬(DE.intersectsLine BC))
    (h16 : a.onLine AL) (h17 : ¬(AL.intersectsLine BD)) (h18 : ¬(a.onLine BD)) :
    AL.intersectsLine DE := by
  euclid_finish

end Elements.Book1

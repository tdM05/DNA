import SystemE

namespace Elements.Book1

-- b.sameSide a CK, since AB ∥ CK and a,b both on AB
theorem helper_1_47_ss4c (a b c k : Point) (AB BC AC CK : Line)
    (h1 : a.onLine AB) (h2 : b.onLine AB) (h3 : a ≠ b)
    (h4 : b.onLine BC) (h5 : c.onLine BC)
    (h6 : c.onLine AC) (h7 : a.onLine AC)
    (h10 : c.onLine CK) (h11 : k.onLine CK)
    (h16 : ∠ a:c:k = ∟) (h18 : ∠ b:a:c = ∟)
    (h21 : ¬(CK.intersectsLine AB))
    (h26 : ¬(a.onLine CK)) (h27 : ¬(b.onLine CK)) :
    b.sameSide a CK := by
  euclid_finish

end Elements.Book1

import SystemE

namespace Elements.Book1

-- k.sameSide a BC, mirror of ss3 (AC-square, between b a h, CK ∥ AB)
theorem helper_1_47_ss3c (a b c h k : Point) (AB BC AC CK HK AH : Line)
    (h1 : a.onLine AB) (h2 : b.onLine AB) (h3 : a ≠ b)
    (h4 : b.onLine BC) (h5 : c.onLine BC)
    (h6 : c.onLine AC) (h7 : a.onLine AC)
    (h10 : c.onLine CK) (h11 : k.onLine CK)
    (h12 : h.onLine HK) (h13 : k.onLine HK)
    (h14 : h.onLine AH) (h15 : a.onLine AH)
    (h16 : ∠ a:c:k = ∟) (h17 : ∠ c:a:h = ∟) (h18 : ∠ b:a:c = ∟)
    (h19 : ¬(h.onLine AC)) (h20 : ¬(b.onLine AC)) (h21 : ¬(h.sameSide b AC))
    (h22 : h.sameSide a CK)
    (h23 : ¬(CK.intersectsLine AB)) (h24 : ¬(HK.intersectsLine AC))
    (h25 : between b a h)
    (h26 : ¬(a.onLine BC)) (h27 : ¬(k.onLine BC)) :
    k.sameSide a BC := by
  euclid_finish

end Elements.Book1

import SystemE

namespace Elements.Book1

-- CK ∥ AB  (CK ∥ AH, and AH = AB since b,a,h collinear)
theorem helper_1_47_ckab (a b c h k : Point) (AB AH CK : Line)
    (h1 : a.onLine AB) (h2 : b.onLine AB) (h3 : a ≠ b)
    (h4 : a.onLine AH) (h5 : h.onLine AH)
    (h6 : between b a h) (h7 : ¬(AH.intersectsLine CK))
    (h8 : c.onLine CK) (h9 : k.onLine CK) (h10 : ¬(a.onLine CK)) :
    ¬(AB.intersectsLine CK) := by
  euclid_finish

end Elements.Book1

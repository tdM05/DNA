import SystemE

set_option systemE.solverTime 25

namespace Elements.Book1

theorem helper_1_47_step20 (a b c f g h k : Point)
    (GF AB AG BF HK AC AH CK : Line)
    (h1 : g.onLine GF) (h2 : f.onLine GF)
    (h3 : a.onLine AB) (h4 : b.onLine AB)
    (h5 : g.onLine AG) (h6 : a.onLine AG)
    (h7 : f.onLine BF) (h8 : b.onLine BF)
    (h9 : f ≠ b) (h10 : g.sameSide a BF)
    (h11 : ¬(GF.intersectsLine AB)) (h12 : ¬(AG.intersectsLine BF))
    (h13 : ∠ b:a:g = ∟) (h14 : |(a─g)| = |(a─b)|) (h15 : |(g─f)| = |(a─b)|)
    (h16 : h.onLine HK) (h17 : k.onLine HK)
    (h18 : a.onLine AC) (h19 : c.onLine AC)
    (h20 : h.onLine AH) (h21 : a.onLine AH)
    (h22 : k.onLine CK) (h23 : c.onLine CK)
    (h24 : k ≠ c) (h25 : h.sameSide a CK)
    (h26 : ¬(HK.intersectsLine AC)) (h27 : ¬(AH.intersectsLine CK))
    (h28 : ∠ c:a:h = ∟) (h29 : |(a─h)| = |(a─c)|) (h30 : |(h─k)| = |(a─c)|) :
    (Triangle.area △ a:g:f + Triangle.area △ a:f:b = |(b─a)| * |(b─a)|) ∧
      (Triangle.area △ a:h:k + Triangle.area △ a:k:c = |(a─c)| * |(a─c)|) := by
  euclid_apply (rectangle_area g f a b GF AB AG BF)
  euclid_apply (rectangle_area h k a c HK AC AH CK)
  euclid_finish

end Elements.Book1

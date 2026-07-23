import SystemE

namespace Elements.Book1

theorem helper_1_47_step20 (a b c f g h k : Point) (GF AB AG BF HK AC AH CK : Line)
    (g1 : g.onLine GF) (g2 : f.onLine GF)
    (g3 : a.onLine AB) (g4 : b.onLine AB)
    (g5 : g.onLine AG) (g6 : a.onLine AG)
    (g7 : f.onLine BF) (g8 : b.onLine BF) (g9 : f ≠ b)
    (g10 : g.sameSide a BF)
    (g11 : ¬(GF.intersectsLine AB)) (g12 : ¬(AG.intersectsLine BF))
    (g13 : ∠ b:a:g = ∟) (g14 : |(g─f)| = |(a─b)|) (g15 : |(a─g)| = |(a─b)|)
    (k1 : h.onLine HK) (k2 : k.onLine HK)
    (k3 : a.onLine AC) (k4 : c.onLine AC)
    (k5 : h.onLine AH) (k6 : a.onLine AH)
    (k7 : k.onLine CK) (k8 : c.onLine CK) (k9 : k ≠ c)
    (k10 : h.sameSide a CK)
    (k11 : ¬(HK.intersectsLine AC)) (k12 : ¬(AH.intersectsLine CK))
    (k13 : ∠ c:a:h = ∟) (k14 : |(h─k)| = |(a─c)|) (k15 : |(a─h)| = |(a─c)|) :
    (Triangle.area △ a:g:f + Triangle.area △ a:f:b = |(b─a)| * |(b─a)|) ∧
      (Triangle.area △ a:h:k + Triangle.area △ a:k:c = |(a─c)| * |(a─c)|) := by
  refine ⟨?_, ?_⟩
  · clear k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 k14 k15
    euclid_apply (rectangle_area g f a b GF AB AG BF)
    euclid_finish
  · clear g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15
    euclid_apply (rectangle_area h k a c HK AC AH CK)
    euclid_finish

end Elements.Book1

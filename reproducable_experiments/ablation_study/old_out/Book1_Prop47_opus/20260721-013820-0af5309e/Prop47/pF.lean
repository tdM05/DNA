import SystemE

namespace Elements.Book1

theorem probe_F (a b c f g m : Point) (AB BC AC BF GF AG AL : Line)
    (h1 : a.onLine AB) (h2 : b.onLine AB) (h3 : a ≠ b)
    (h4 : b.onLine BC) (h5 : c.onLine BC)
    (h6 : c.onLine AC) (h7 : a.onLine AC)
    (h10 : b.onLine BF) (h11 : f.onLine BF)
    (h12 : g.onLine GF) (h13 : f.onLine GF)
    (h14 : g.onLine AG) (h15 : a.onLine AG)
    (h16 : ∠ a:b:f = ∟) (h17 : ∠ b:a:g = ∟) (h18 : ∠ b:a:c = ∟)
    (h19 : ¬(g.onLine AB)) (h20 : ¬(c.onLine AB)) (h21 : ¬(g.sameSide c AB))
    (h22 : g.sameSide a BF)
    (h23 : ¬(BF.intersectsLine AC)) (h24 : ¬(GF.intersectsLine AB))
    (h25 : between c a g)
    (h26 : ¬(a.onLine BC)) (h27 : ¬(f.onLine BC)) :
    f.sameSide a BC := by
  euclid_finish

end Elements.Book1

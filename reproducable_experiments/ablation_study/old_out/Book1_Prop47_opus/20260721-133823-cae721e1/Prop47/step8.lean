import SystemE

set_option systemE.solverTime 25

namespace Elements.Book1

theorem helper_1_47_step8 (a b c d f g : Point) (AB BC BD BF : Line)
    (h1 : ∠ d:b:c + ∠ a:b:c = ∠ f:b:a + ∠ a:b:c)
    (h2 : a.onLine AB) (h3 : b.onLine AB) (h4 : b.onLine BC) (h5 : c.onLine BC)
    (h6 : b.onLine BD) (h7 : d.onLine BD) (h8 : b.onLine BF) (h9 : f.onLine BF)
    (h10 : ∠ c:b:d = ∟) (h11 : ∠ a:b:f = ∟) (h12 : ∠ b:a:c = ∟)
    (h13 : ¬(d.onLine BC)) (h14 : ¬(a.onLine BC)) (h15 : ¬(d.sameSide a BC))
    (h16 : ¬(g.onLine AB)) (h17 : ¬(c.onLine AB)) (h18 : ¬(g.sameSide c AB))
    (h19 : between c a g) (h20 : ¬(a.onLine BD)) :
    ∠ d:b:a = ∠ f:b:c := by
  euclid_finish

end Elements.Book1

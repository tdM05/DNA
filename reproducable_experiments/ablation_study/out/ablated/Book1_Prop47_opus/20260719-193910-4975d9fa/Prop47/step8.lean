import SystemE

namespace Elements.Book1

theorem helper_1_47_step8 (a b c d f : Point) (AB BC BD BF : Line)
    (h1 : ∠ d:b:c + ∠ a:b:c = ∠ f:b:a + ∠ a:b:c)
    (hbd1 : b.onLine BD) (hbd2 : d.onLine BD)
    (hbc1 : b.onLine BC) (hbc2 : c.onLine BC)
    (hab1 : b.onLine AB) (hab2 : a.onLine AB)
    (hbf1 : b.onLine BF) (hbf2 : f.onLine BF)
    (hcAB : ¬(c.onLine AB)) (haBC : ¬(a.onLine BC))
    (hs1 : d.sameSide c AB) (hs2 : a.sameSide c BD)
    (hs3 : f.sameSide a BC) (hs4 : c.sameSide a BF) :
    ∠ d:b:a = ∠ f:b:c := by
  euclid_finish

end Elements.Book1
